type sym = string

type linqual = Linear
              | Unrestricted
              [@@deriving show, eq, ord]

type qual_type = QualType of linqual * pre_type
                [@@deriving show, eq, ord]

and pre_type = TBool
              | TInt
              | TArr of qual_type * qual_type
              | TPair of qual_type * qual_type
              | TSum  of qual_type * qual_type
              | TRec  of string * qual_type
              | TVar of string
              [@@deriving show, eq, ord]

type term = Var of string
           | TIf of term * term * term
           | Lam of linqual * sym * qual_type * term
           | Pair of linqual * term * term
           | App of term * term
           | LInt of linqual * int
           | LBool of linqual * bool
           | Split of term * sym * sym * term
           | InL of linqual * pre_type * term
           | InR of linqual * pre_type * term
           | TCase of term * sym * term * sym * term
           | TRoll of pre_type * term
           | TUnRoll of term
           | TFunRec of sym * sym * pre_type * pre_type * term
           [@@deriving show, eq, ord]

type context = (sym * qual_type) list
               [@@deriving show]

type type_error = Err of string

(*--------------------------------------------------------------------*)

let extend_context ct vt = vt :: ct

let context_diff ct v qt = match qt with
  | QualType (Linear, _) ->
          begin
           match (List.assoc_opt v ct) with
            | Some _ -> Error (Err ("Linear Var: " ^ v ^ " unused"))
            | None -> Ok ct
          end
  | QualType (Unrestricted,  _) ->
          begin
          match List.assoc_opt v ct with
          | None   -> Error (Err ("Unrestricted var '" ^ v ^ "' not found"))
          | Some _ ->  Ok (List.remove_assoc v ct)
          end

let containment_check lq qt =
  match (lq, qt) with
    | (Linear, QualType (Linear, _)) -> true
    | (Linear, QualType (Unrestricted, _)) -> true
    | (Unrestricted, QualType (Unrestricted, _)) -> true
    | (Unrestricted,  QualType (Linear, _)) -> false

(* declarative bind from the Result module *)
let ( let* ) = Result.bind

(* The equivalent of Haskell's unless *)
let unless cond msg = if cond then Ok () else Error (Err msg)

let rec subs_type (sym : string) rep = function
  | QualType (qt, TVar sym') ->
      if sym' = sym then rep
      else QualType (qt, TVar sym')

  | QualType (qt, TArr (fn_ty, arg_ty)) ->
      QualType (qt, TArr (subs_type sym rep fn_ty,
                          subs_type sym rep arg_ty))

  | QualType (qt, TPair (fst_ty, snd_ty)) ->
      QualType (qt, TPair (subs_type sym rep fst_ty,
                           subs_type sym rep snd_ty))

  | QualType (qt, TSum (left_ty, right_ty)) ->
      QualType (qt, TSum (subs_type sym rep left_ty,
                          subs_type sym rep right_ty))

  | QualType (qt, TRec (sym', rec_ty)) ->
      if String.equal sym' sym then
        QualType (qt, TRec (sym, rec_ty))   (* shadowed — stop *)
      else
        QualType (qt, TRec (sym', subs_type sym rep rec_ty))

  | QualType (qt, TBool) -> QualType (qt, TBool)
  | QualType (qt, TInt)  -> QualType (qt, TInt)


(* ------------------------------------------------------------------*)
let rec check ct t =
  match t with

  | LBool (q, _) -> Ok ((QualType (q, TBool), ct))

  | LInt (q, _) -> Ok ((QualType (q, TInt), ct))

  | Var b -> begin
               match (List.assoc_opt b ct) with
               | Some (QualType (Unrestricted, _) as qt) -> Ok (qt, ct)
               | Some (QualType (Linear,  _) as unt)
                                -> Ok (unt, List.remove_assoc b ct)
               | None -> Error (Err "Var not in context")
    end

  | Lam (q, x, qt, body) ->
         let ct_extended = extend_context ct (x, qt) in
         let* (body_ty, ct1) = check ct_extended body in
         let* ct2 = context_diff ct1 x qt in
         Result.bind
             (if q = Unrestricted then
                 unless (ct1 <> ct2) "Unrestricted variables incorrectly consumed"
             else Ok ())
            (fun _ -> Ok (QualType (q, TArr (qt, body_ty)), ct2))

  | TIf (t1, t2, t3) ->
        let* (bool_type, context') =  check ct t1 in
         begin
        match bool_type with
        | QualType (_, TBool)  ->
         let* (t2', context'') =  check context' t2 in
         let* (t3', context''') = check context' t3 in
         Result.bind
           (Result.get_ok (unless (context'' = context''')
           "If branch contexts differ");
            Result.get_ok (unless (t2' = t3') "If branch types differ");
            Ok ())
           (fun _ -> Ok (t2', context''))
        | _ -> Error (Err "Term in If guard does not evaluate to a boolean")
         end


  | Pair (qt, t1, t2) ->
       let* (pair_ty1, ct') = check ct t1 in
       let* (pair_ty2, ct'') = check ct' t2 in
       Result.bind
       (Result.get_ok (unless (containment_check qt pair_ty2)
       "Containment check for first term of a Pair fails");
        Result.get_ok (unless (containment_check qt pair_ty2)
        "Containment check for second term of a Pair fails");
        Ok ())
        (fun _ -> Ok (QualType (qt, TPair (pair_ty1, pair_ty2)), ct''))


  | Split (split_term, x, y, in_term) ->
    let* (split_ty, ct') = check ct split_term in
     begin match split_ty  with
      | QualType (_, (TPair (qt1, qt2)))->
        let ct'' = extend_context ct' (x, qt1) in
        let ct''' = extend_context ct'' (y, qt2) in
        let* (type_result, ct'''') = check ct''' in_term in
        let* context_diff1 = context_diff ct'''' x qt1 in
        let* context_diff2 = context_diff ct'''' y qt2 in
        Result.bind (unless (context_diff1 = context_diff2)
                      "types added to contexts after splitting are not removed")
        (fun _ -> Ok (type_result, context_diff2))
     | _ -> Error (Err "Cannot split a non-pair")
     end

  | App (t1, t2) ->
       let* (result_ty, ct')  = check ct t1 in
       begin match result_ty with
        | QualType (_ , (TArr (qt1, qt2))) ->
          let* (result_ty2, ct'') = check ct' t2 in
          Result.bind (unless (result_ty2 = qt1) "Type mismatch in App")
            (fun _ -> Ok (qt2, ct''))
        | _ -> Error (Err "Trying to apply non-function")
        end



  | InL (qt, pt, inl_term) ->
    let* (inl_type, ctx') = check ct inl_term in
    begin match pt with
     | TSum (sum_type1, sum_type2) ->
       let* () = unless (inl_type = sum_type1)
                 "Left injection does not match the assigned left type" in
       let* () = unless (containment_check qt sum_type1)
                 "Containment check for left type of sum fails" in
       let* () = unless (containment_check qt sum_type2)
                   "Containment check for right type of sum fails" in
       Ok (QualType (qt, TSum (sum_type1, sum_type2)), ctx')
     | _ -> Error (Err "InL annotation is not a sum type")
    end

  | InR (qt, pt, inr_term) ->
    let* (inr_type, ctx') = check ct inr_term in
    begin match pt with
     | TSum (sum_type1, sum_type2) ->
       let* () = unless (inr_type = sum_type2)
                   "Right injection does not match the assigned right type" in
       let* () = unless (containment_check qt sum_type1)
                   "Containment check for left type of sum fails" in
       let* () = unless (containment_check qt sum_type2)
                   "Containment check for right type of sum fails" in
       Ok (QualType (qt, TSum (sum_type1, sum_type2)), ctx')
     | _ -> Error (Err "InR annotation is not a sum type")
    end

  | TCase (case_term, sym_l, inl_term, sym_r, inr_term) ->
    let* (case_ty, ctx') = check ct case_term in
    begin match case_ty with
     | QualType (_, TSum (sum_type1, sum_type2)) ->
       let ctx_l = extend_context ctx' (sym_l, sum_type1) in
       let ctx_r = extend_context ctx' (sym_r, sum_type2) in
       let* (inl_type, ctx_l') = check ctx_l inl_term in
       let* (inr_type, ctx_r') = check ctx_r inr_term in
       let* ctx_diff_l = context_diff ctx_l' sym_l sum_type1 in
       let* ctx_diff_r = context_diff ctx_r' sym_r sum_type2 in
       let* () = unless (inl_type = inr_type)
                   "The inferred types for the two case branches do not match" in
       let* () = unless (ctx_diff_l = ctx_diff_r)
                   "The type contexts for the two case branches differ" in
       Ok (inl_type, ctx_diff_l)
     | _ -> Error (Err "Case scrutinee does not have a sum type")
    end


  | TRoll (pt, roll_term) ->
    begin match pt with
     | TRec (sym_rec, (QualType (qt, _) as inner_ty)) ->
       let* (term_ty, ctx') = check ct roll_term in
       let unrolled = subs_type sym_rec (QualType (qt, pt)) inner_ty in
       let* () = unless (term_ty = unrolled)
                   "Roll term type does not match unrolled type" in
       Ok (QualType (qt, pt), ctx')
     | _ -> Error (Err "Roll annotation is not a recursive type")
    end

  | TUnRoll unroll_term ->
    let* (pt_rec, ctx') = check ct unroll_term in
    begin match pt_rec with
     | QualType (_, (TRec (sym_rec, QualType (qt, pt_rec_inner)) as pt)) ->
       let unrolled = subs_type sym_rec
                        (QualType (qt, pt))
                        (QualType (qt, pt_rec_inner)) in
       Ok (unrolled, ctx')
     | _ -> Error (Err "Unroll term does not have a recursive type")
    end


  | TFunRec (sym_f, sym_x, pt1, qt2, rec_term) ->
    let* () =
      unless (List.for_all (fun (_, QualType (q, _)) -> q = Unrestricted) ct)
        "Context contains linear variables (recursive functions must be unrestricted)" in
    let arg_ty = QualType (Unrestricted, pt1) in
    let ret_ty = QualType (Unrestricted, qt2) in
    let f_ty   = QualType (Unrestricted, TArr (arg_ty, ret_ty)) in
    (* Extend context with argument x and recursive name f *)
    let ctx'  = extend_context ct  (sym_x, arg_ty) in
    let ctx'' = extend_context ctx' (sym_f, f_ty)   in
    let* (body_ty, ctx''') = check ctx'' rec_term in
    begin match body_ty with
     | QualType (Unrestricted, TArr (ut1, qt')) ->
       let* () = unless (ut1 = arg_ty)
                   "Recursive function input type does not match annotation" in
       let* () = unless (qt' = ret_ty)
                   "Recursive function return type does not match annotation" in
       let* ctx_x = context_diff ctx'''  sym_x arg_ty in
       let* ctx_f = context_diff ctx_x   sym_f f_ty   in
       Ok (f_ty, ctx_f)
     | _ -> Error (Err "Recursive function body does not have an unrestricted function type")
    end

let check_expr =
    let x =  TIf ((LBool (Unrestricted, true)),
                (LInt (Linear, 1)), (LInt (Linear, 2))) in
    check [] x
