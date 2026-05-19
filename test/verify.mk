# Auxiliary makefile invoked inside each out/<test>/ directory.
# Verifies all .fst files using F*'s --dep full for dependency ordering.
#
# Expected variables (passed from parent):
#   FSTAR_EXE  — path to the F* runner script
#   CACHE_DIR  — directory for .fst.checked files

FSTAR_EXE ?= ../../opt/run-fstar.sh
CACHE_DIR  ?= cache

FSTAR = $(FSTAR_EXE) \
	--cache_checked_modules \
	--cache_dir $(CACHE_DIR) \
	--already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore \
	--include .

FST_FILES := $(wildcard *.fst)
ALL_CHECKED_FILES := $(patsubst %.fst,$(CACHE_DIR)/%.fst.checked,$(FST_FILES))

.PHONY: all
all: $(ALL_CHECKED_FILES)

$(shell mkdir -p $(CACHE_DIR))

# Compute inter-module dependencies via F* --dep full.
# The generated .depend provides per-target prerequisite rules like:
#   cache/Func_foo.fst.checked: Func_foo.fst cache/Struct_bar.fst.checked ...
.depend: $(FST_FILES)
	$(FSTAR) --dep full $(FST_FILES) --output_deps_to $@

include .depend

$(CACHE_DIR)/%.fst.checked:
	@echo "Verifying $*.fst"
	$(FSTAR) $(notdir $*.fst)
	@touch -c $@

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR) .depend
