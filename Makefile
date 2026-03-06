.DEFAULT_GOAL := invoke-makefile

KNOWNTARGETS := CoqMakefile
KNOWNFILES := Makefile _CoqProject

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

CoqMakefile: _CoqProject
	@rocq makefile -f _CoqProject -o CoqMakefile

.PHONY: invoke-coqmakefile $(KNOWNFILES)

%: invoke-coqmakefile
	@true