# Variables
OCAMLC = ocamlc
SOURCES = lincheck.ml
OBJS = $(SOURCES:.ml=.cmo)
EXEC = check

# Default rule
all: $(EXEC)

# Rule to link the executable
$(EXEC): $(OBJS)
	$(OCAMLC) -o $(EXEC) $(OBJS)

# Generic rule for compiling .ml files to .cmo
%.cmo: %.ml
	$(OCAMLC) -c $<

# Clean up
clean:
	rm -f *.cmo *.cmi $(EXEC)
