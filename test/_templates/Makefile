.PHONY: all translate verify compile clean

C2PULSE ?= ../../target/debug/pal
CACHE_DIR ?= _cache
OUT_DIR ?= out
OBJ_DIR ?= obj

C_FILES := $(wildcard *.c)
H_FILES := $(wildcard *.h)
PAL_OPTS :=

# The memory model's own modules are checked once, in `pulse/`, and found from
# there rather than re-verified in every test.
FSTAR_RUN := ../../opt/run-fstar.sh
PULSE_CACHE := ../../pulse/_cache
FSTAR_EXE ?= $(FSTAR_RUN) --include $(PULSE_CACHE)
HELPERS := helpers

# If there's an include/ directory, add -I include
ifneq ($(wildcard include),)
INCLUDES += -I include
endif
PAL_OPTS += $(INCLUDES)

# Extra preprocessor flags (-D, -I) for this test, passed to both PAL and cc.
ifneq ($(wildcard extra_opts),)
EXTRA_OPTS := $(shell cat extra_opts)
PAL_OPTS += $(EXTRA_OPTS)
endif

# Translation-only options, such as selecting a named function body.
ifneq ($(wildcard pal_opts),)
PAL_OPTS += $(shell cat pal_opts)
endif

all: verify compile

ifneq ($(wildcard native-check.c),)
.PHONY: native-check
all: native-check
native-check:
	@mkdir -p $(OBJ_DIR)
	$(CC) $(INCLUDES) $(EXTRA_OPTS) $(C_FILES) -o $(OBJ_DIR)/native-check
	$(OBJ_DIR)/native-check
endif

ifneq ($(wildcard reverse-order),)
.PHONY: linkage-controls
all: linkage-controls
linkage-controls: verify
	python3 ../check-linkage.py "$(abspath $(C2PULSE))" "$(abspath $(FSTAR_RUN)) --include $(abspath $(PULSE_CACHE))" "$(abspath $(OUT_DIR))" "$(CC)"
endif

translate: $(OUT_DIR)/.stamp

$(OUT_DIR)/.stamp: $(C_FILES) $(H_FILES) $(C2PULSE) pal.h $(wildcard extra_opts pal_opts)
	@mkdir -p $(OUT_DIR)
	$(C2PULSE) $(PAL_OPTS) --outdir $(OUT_DIR) $(C_FILES)
	@touch $@

# A negative test carries a `should-fail` file: verification must fail, and
# every line of that file must appear in the output. Without the second half a
# test could start failing for some unrelated reason and still look like it was
# doing its job.
ifneq ($(wildcard should-fail),)
verify: $(OUT_DIR)/.stamp
	@if $(MAKE) --no-print-directory -f ../verify.mk \
		OUT_DIR=$(OUT_DIR) FSTAR_EXE="$(FSTAR_EXE)" CACHE_DIR=$(CACHE_DIR) \
		HELPERS=$(HELPERS) >$(OUT_DIR)/verify.log 2>&1; then \
		echo "ERROR: $(CURDIR) verified, but should-fail says it must not" >&2; \
		exit 1; \
	fi; \
	while IFS= read -r pat; do \
		[ -z "$$pat" ] && continue; \
		if ! grep -qF -- "$$pat" $(OUT_DIR)/verify.log && \
			! { test "$$OS" = Windows_NT && \
				sed -E '/^\* Error [0-9]+ at /s|\\|/|g' $(OUT_DIR)/verify.log | \
				grep -qF -- "$$pat"; }; then \
			echo "ERROR: $(CURDIR) failed, but not for the expected reason:" >&2; \
			echo "       no line of the output contains '$$pat'" >&2; \
			exit 1; \
		fi; \
	done < should-fail; \
	echo "Failed as expected: $(CURDIR)"
else
verify: $(OUT_DIR)/.stamp
	@$(MAKE) --no-print-directory -f ../verify.mk \
		OUT_DIR=$(OUT_DIR) FSTAR_EXE="$(FSTAR_EXE)" CACHE_DIR=$(CACHE_DIR) \
		HELPERS=$(HELPERS) \
		EXPECTED_FAILURES_FILE=expected-verification-failures.txt \
		EXPECTED_FAILURE_TEXT_FILE=expected-verification-error.txt
endif

compile: $(patsubst %.c,$(OBJ_DIR)/%.o,$(C_FILES))

$(OBJ_DIR)/%.o: %.c $(C_FILES) $(H_FILES)
	@mkdir -p $(OBJ_DIR)
	$(CC) $(INCLUDES) $(EXTRA_OPTS) -c $< -o $@

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR) $(OBJ_DIR) .depend
