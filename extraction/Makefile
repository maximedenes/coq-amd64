define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

ifdef USERINSTALL
  XDG_DATA_HOME?="$(HOME)/.local/share"
  COQLIBINSTALL=$(XDG_DATA_HOME)/coq
else
  COQLIBINSTALL="${COQLIB}user-contrib"
endif

INCLUDES=-I $(COQLIB)user-contrib/OCamlBind
OCAMLC=ocamlc -rectypes -g $(INCLUDES)
OCAMLOPT=ocamlopt -rectypes $(INCLUDES)
OCAMLDEP=ocamldep
OCAMLYACC=ocamlyacc -v
OCAMLLEX=ocamllex

LIBS=

CMX=Bool.cmx Ascii.cmx Datatypes.cmx Nat.cmx String0.cmx \
	BinPosDef.cmx BinPos.cmx BinNat.cmx BinInt.cmx \
    ssrbool.cmx ssrnat.cmx seq.cmx eqtype.cmx fintype.cmx \
	tuple.cmx bitsrep.cmx \
	bitsops.cmx monad.cmx reader.cmx writer.cmx \
    reg.cmx instr.cmx program.cmx ../src/printinstr.cmx

CMO=$(CMX:.cmx=.cmo)

PLUGIN=../src/printinstr.cmxs

$(PLUGIN): $(CMX) $(CMO)
	$(OCAMLOPT) -linkall -shared -o $(PLUGIN) $(LIBS) $(CMX)

.SUFFIXES: .ml .mli .cmo .cmx .cmi

.mli.cmi:
	$(OCAMLOPT) -c $*.mli
.ml.cmx:
	$(OCAMLOPT) -c $*.ml
.ml.cmo:
	$(OCAMLC) -c $*.ml

install:
	for i in $(CMX); do \
	  install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/Amd64/$$i`"; \
	  install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Amd64/`basename $$i`; \
	done
	for i in $(PLUGIN); do \
	  install -m 0744 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Amd64/`basename $$i`; \
	done

clean:
	rm -f $(GENERATED) $(PLUGIN) *.cm*

.depend:
	$(OCAMLDEP) *.ml > .depend

include .depend
