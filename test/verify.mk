# Auxiliary makefile for F* verification.
# Invoked from per-test Makefiles with:
#   OUT_DIR   — directory containing .fst/.fsti files
#   FSTAR_EXE — path to the F* runner script
#   CACHE_DIR — directory for .fst.checked files

FSTAR_EXE ?= ../../opt/run-fstar.sh
CACHE_DIR  ?= _cache
OUT_DIR    ?= out
EXPECTED_FAILURES_FILE ?=

FSTAR = $(FSTAR_EXE) \
	--cache_checked_modules \
	--cache_dir $(CACHE_DIR) \
	--already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore \
	--include $(OUT_DIR)

ifneq ($(wildcard helpers),)
FSTAR += --include helpers
endif

FST_FILES := $(wildcard $(OUT_DIR)/*.fst)
FSTI_FILES := $(wildcard $(OUT_DIR)/*.fsti)
EXPECTED_FAILURE_MODULES := $(if $(wildcard $(EXPECTED_FAILURES_FILE)),$(shell sed 's/#.*//; /^[[:space:]]*$$/d; s/[[:space:]]//g; s/\.fst$$//' $(EXPECTED_FAILURES_FILE)))
EXPECTED_FAILURE_FST_FILES := $(addprefix $(OUT_DIR)/,$(addsuffix .fst,$(EXPECTED_FAILURE_MODULES)))
NORMAL_FST_FILES := $(filter-out $(EXPECTED_FAILURE_FST_FILES),$(FST_FILES))
ALL_CHECKED_FILES := $(patsubst $(OUT_DIR)/%.fst,$(CACHE_DIR)/%.fst.checked,$(NORMAL_FST_FILES)) \
                     $(patsubst $(OUT_DIR)/%.fsti,$(CACHE_DIR)/%.fsti.checked,$(FSTI_FILES))

.PHONY: all
all: $(ALL_CHECKED_FILES) expected-verification-failures

$(shell mkdir -p $(CACHE_DIR))

.depend: $(FST_FILES) $(FSTI_FILES)
	$(FSTAR) --dep full $(FST_FILES) $(FSTI_FILES) --output_deps_to $@

include .depend

$(CACHE_DIR)/%.fst.checked:
	@echo "Verifying $*.fst"
	$(FSTAR) $<
	@touch -c $@

$(CACHE_DIR)/%.fsti.checked:
	@echo "Verifying $*.fsti"
	$(FSTAR) $<
	@touch -c $@

.PHONY: expected-verification-failures
expected-verification-failures:
	@for m in $(EXPECTED_FAILURE_MODULES); do \
		echo "Expecting verification failure $$m.fst"; \
		if [ ! -f "$(OUT_DIR)/$$m.fst" ]; then \
			echo "ERROR: expected failure module $(OUT_DIR)/$$m.fst does not exist"; \
			exit 1; \
		fi; \
		if $(FSTAR) $(OUT_DIR)/$$m.fst >$(CACHE_DIR)/$$m.expected-failure.log 2>&1; then \
			echo "ERROR: $$m.fst verified but was expected to fail"; \
			cat $(CACHE_DIR)/$$m.expected-failure.log; \
			exit 1; \
		fi; \
	done

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR) .depend
