SHELL      := bash
COQC       := coqc
# COQDEP     := coqdep

.PHONY: all
all: tactics test

.PHONY: tactics
tactics: CoqMakefile
	$(MAKE) -f $<

.PHONY: install
install: CoqMakefile tactics
	$(MAKE) -f $< $@

TEST_SRC := $(sort $(shell find test -iname '*.v'))
TEST_COQC_FLAGS := -Q src CalTac
.PHONY: test
test: $(TEST_SRC:.v=.vo)
$(TEST_SRC:.v=.vo): %.vo: %.v tactics
	$(COQC) $(TEST_COQC_FLAGS) $<

.PHONY: clean
clean:
	if [[ -e CoqMakefile ]]; then \
		$(MAKE) -f CoqMakefile $@; \
	fi
	find . \( -iname '.lia.cache' -o \
		      -iname '*.vo' -o \
		      -iname '*.vok' -o \
		      -iname '*.vos' -o \
		      -iname '*.aux' -o \
		      -iname '*.glob' -o \
		      -iname '*.d' \) \
		-print -delete
	$(RM) CoqMakefile CoqMakefile.conf

CoqMakefile: _CoqProject
	coq_makefile -f $< -o $@
