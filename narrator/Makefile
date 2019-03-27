SRCFILES = src/*.ml src/*.mli

CINAPSFILES = src/*.cinaps

OCAMLFORMAT = ocamlformat \
	--inplace \
	--field-space loose \
	--let-and sparse \
	--let-open auto \
	--type-decl sparse \
	--sequence-style terminator \
	$(SRCFILES) \

OCPINDENT = ocp-indent \
	--inplace \
	$(SRCFILES)

.PHONY: all
all : bin doc

.PHONY: bin
bin :
	dune build

.PHONY: format
format :
	$(OCAMLFORMAT)
	$(OCPINDENT)

.PHONY: cinaps
cinaps :
	cinaps -i $(SRCFILES)
	$(OCAMLFORMAT)
	$(OCPINDENT)

.PHONY: doc
doc :
	dune build @doc
	rm -rf _doc/
	cp -r _build/default/_doc .

.PHONY: browse_doc
browse_doc : doc
	$$BROWSER _doc/_html/index.html

.PHONY: test
test :
	dune runtest --force

.PHONY: coverage
coverage : clean
	BISECT_ENABLE=YES dune runtest --force
	bisect-ppx-report -I _build/default/ -html _coverage/ \
		`find . -name 'bisect*.out'`

.PHONY: browse_coverage
browse_coverage : coverage
	$$BROWSER _coverage/index.html

.PHONY : clean
clean :
	rm -f `find . -name 'bisect*.out'`
	dune clean
