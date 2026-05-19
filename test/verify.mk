# Auxiliary makefile invoked inside each out/<test>/ directory.
# Verifies all .fst files, producing .fst.checked artifacts.
#
# Expected variables (passed from parent):
#   FSTAR_EXE  — path to the F* runner script
#   CACHE_DIR  — directory for .fst.checked files

FSTAR_EXE ?= ../../opt/run-fstar.sh
CACHE_DIR  ?= cache

FST_FILES := $(wildcard *.fst)
CHECKED   := $(patsubst %.fst,$(CACHE_DIR)/%.fst.checked,$(FST_FILES))

.PHONY: all
all: $(CHECKED)

$(shell mkdir -p $(CACHE_DIR))

# Each .fst.checked depends on all .fst files in this directory (conservative).
# F* with --ext fly_deps resolves the actual dependency order internally;
# we just need to ensure all sources are present before verification starts.
$(CACHE_DIR)/%.fst.checked: %.fst $(FST_FILES)
	@echo "Verifying $<"
	$(FSTAR_EXE) \
		--cache_checked_modules \
		--cache_dir $(CACHE_DIR) \
		--already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore \
		--include . \
		$<

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR)
