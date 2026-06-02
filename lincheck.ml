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
  | QualType (Unrestricted,  _) -> Ok (List.remove_assoc v ct)

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

(* ------------------------------------------------------------------*)
let rec check ct t =
  match t with
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
  begin
   match (check ct t1) with
    | Ok (bool_type, context') ->
       begin
        match bool_type with
        | QualType (_, TBool)  ->
         begin
          match (check context' t2, check context' t3) with
          | Ok (t1', context''), Ok (t2', context''') ->
            if t1' <> t2' then Error (Err "Branch types differ")
            else if context'' <> context'''
                 then Error (Err "Branch contexts differ")
                 else Ok (t2', context'')
          | _ -> Error (Err "branch terms in If term do not typecheck")
         end
         | _ -> Error (Err "Condition in If term does not typecheck to a boolean")
       end
    | Error (Err _)  -> Error (Err "Condition in If term does not typecheck")
  end


  |  Pair (qt, t1, t2) ->
   begin
    match (check ct t1) with
     | Ok (pair_ty1, ct') ->
      begin
       match (check ct' t2) with
        | Ok (pair_ty2, ct'')  ->
          if not (containment_check qt pair_ty2) then
            Error (Err "Containment check for first term of a Pair fails")
          else if (containment_check qt pair_ty2) then
            Error (Err "Containment check for second term of a Pair fails")
          else
            Ok (QualType (qt, TPair (pair_ty1, pair_ty2)), ct'')
        | Error (Err _) -> Error (Err "The first term in a Pair does not typecheck")
        end
    | Error (Err _) -> Error (Err "Check for error in boolean term of If term")
   end

  | Split (split_term, x, y, in_term) ->
    begin match (check ct split_term) with
    | Ok (split_ty, ct') ->
     begin match split_ty  with
      | QualType (_, (TPair (qt1, qt2)))->
        let ct'' = extend_context ct' (x, qt1) in
        let ct''' = extend_context ct'' (y, qt2) in
         begin match (check ct''' in_term) with
           | Ok (type_result, ct'''') ->
             begin match (context_diff ct'''' x qt1) with
             | Ok context_diff1 ->
                 begin
                   match (context_diff context_diff1 y qt2) with
                   | Ok context_diff2 -> Ok (type_result, context_diff2)
                   | _ -> Error (Err "Context-diff fail: check linear var use")
                 end
             | _ -> Error (Err "Context-diff fail: check linear var use")
             end
           | _ -> Error (Err "Pair term did not typecheck")
         end
      | _  -> Error (Err "Pair term did not evaluate to a a pair type")
     end
    | Error (Err _) -> Error (Err "Cannot split a non-pair")
    end

  | App (t1, t2) ->
    begin
     match (check ct t1) with
     | Ok (result_ty, ct') ->
       begin match result_ty with
        | QualType (_ , (TArr (qt1, qt2))) ->
          begin match (check ct' t2) with
           | Ok (result_ty2, ct'') ->
             if (result_ty2 <> qt1) then
                 Error (Err "Type mismatch in App")
             else Ok (qt2, ct'')
           | Error (Err _) -> Error (Err "App: Term in argument postion does not
typecheck")
          end
        |  _ -> Error (Err "App: Term in function position does not typecheck to an
        arrow type")
       end
    | Error (Err _) -> Error (Err "Trying to apply non-function")
    end


  | LBool (q, _) ->
         Ok ((QualType (q, TBool), ct))

  | LInt (q, _) -> Ok ((QualType (q, TInt), ct))


let check_expr =
    let x =  TIf ((LBool (Unrestricted, true)),
                (LInt (Linear, 1)), (LInt (Linear, 2))) in
    check [] x
