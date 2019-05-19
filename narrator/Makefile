SRCFILES = src/*.ml*

CINAPSFILES = src/*.cinaps

OCAMLFORMAT = ocamlformat \
	--inplace \
	--field-space loose \
	--let-and sparse \
	--let-open auto \
	--type-decl sparse \
	--sequence-style terminator \
	$(SRCFILES) \
	$(CINAPSFILES)

OCPINDENT = ocp-indent \
	--inplace \
	$(SRCFILES) \
	$(CINAPSFILES)

.PHONY: all
all: build

.PHONY: build
build:
	dune build @js --profile dev
	cp -r node_modules/        _build/default/src/
	cp    html/file_strings.js _build/default/src/
	cp    html/index.html      _build/default/src/
ifneq ($(DEBUG), 1)
	find _build/ -name "*.ml"       -type f -delete
	find _build/ -name "*.mli"      -type f -delete
	find _build/ -name "*.mly"      -type f -delete
	find _build/ -name "*.mll"      -type f -delete
	find _build/ -name "*.inferred" -type f -delete
	find _build/ -name "*.mock"     -type f -delete
	find _build/ -name "*.cmi"      -type f -delete
	find _build/ -name "*.bc"       -type f -delete
	rm -r _build/default/src/.narrator.eobjs/
	find _build/ -name ".merlin" -type f -delete
	find _build/ -name ".merlin-exists" -type f -delete
	# javascript-obfuscator _build/default/src/narrator.bc.js \
	# --output _build/default/src/narrator-obfuscated.bc.js
	# mv _build/default/src/narrator-obfuscated.bc.js \
	# _build/default/src/narrator.bc.js
endif

.PHONY: format
format :
	$(OCAMLFORMAT)
	$(OCPINDENT)

.PHONY: cinaps
cinaps :
	cinaps -i $(SRCFILES)
	$(OCAMLFORMAT)
	$(OCPINDENT)
