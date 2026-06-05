# Auxiliary makefile for F* verification.
# Invoked from per-test Makefiles with:
#   OUT_DIR   — directory containing .fst/.fsti files
#   FSTAR_EXE — path to the F* runner script
#   CACHE_DIR — directory for .fst.checked files

FSTAR_EXE ?= ../../opt/run-fstar.sh
CACHE_DIR  ?= _cache
OUT_DIR    ?= out

FSTAR = $(FSTAR_EXE) \
	--cache_checked_modules \
	--cache_dir $(CACHE_DIR) \
	--already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore \
	--include helpers \
	--include $(OUT_DIR)

FST_FILES := $(wildcard $(OUT_DIR)/*.fst)
FSTI_FILES := $(wildcard $(OUT_DIR)/*.fsti)
ALL_CHECKED_FILES := $(patsubst $(OUT_DIR)/%.fst,$(CACHE_DIR)/%.fst.checked,$(FST_FILES)) \
                     $(patsubst $(OUT_DIR)/%.fsti,$(CACHE_DIR)/%.fsti.checked,$(FSTI_FILES))

.PHONY: all
all: $(ALL_CHECKED_FILES)

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

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR) .depend
