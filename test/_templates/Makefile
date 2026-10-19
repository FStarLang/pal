.PHONY: all translate verify compile clean

C2PULSE ?= ../../target/debug/pal
CACHE_DIR ?= _cache
OUT_DIR ?= out
OBJ_DIR ?= obj

C_FILES := $(wildcard *.c)
H_FILES := $(wildcard *.h)
PAL_OPTS :=
SHOULD_FAIL ?= should-fail
STANDALONE ?= $(if $(wildcard standalone),1,0)

ifeq ($(STANDALONE),1)

all: $(C_FILES:.c=.all)
translate: $(C_FILES:.c=.translate)
verify: $(C_FILES:.c=.verify)
compile: $(C_FILES:.c=.compile)
clean: $(C_FILES:.c=.clean)

STANDALONE_TARGETS := $(foreach goal,all translate verify compile clean,$(C_FILES:.c=.$(goal)))
.PHONY: $(STANDALONE_TARGETS)
$(STANDALONE_TARGETS):
	+$(MAKE) --no-print-directory STANDALONE=0 C_FILES=$(basename $@).c \
		OUT_DIR=$(OUT_DIR)/$(basename $@) CACHE_DIR=$(CACHE_DIR)/$(basename $@) \
		OBJ_DIR=$(OBJ_DIR)/$(basename $@) DEPEND=$(OUT_DIR)/$(basename $@)/.depend \
		SHOULD_FAIL=$(if $(wildcard $(basename $@).should-fail),$(basename $@).should-fail,$(SHOULD_FAIL)) \
		$(patsubst .%,%,$(suffix $@))

else

# The memory model's own modules are checked once, in `pulse/`, and found from
# there rather than re-verified in every test.
FSTAR_EXE ?= ../../opt/run-fstar.sh --include ../../pulse/_cache
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

all: verify compile

translate: $(OUT_DIR)/.stamp

$(OUT_DIR)/.stamp: $(C_FILES) $(H_FILES) $(C2PULSE) pal.h
	@mkdir -p $(OUT_DIR)
	$(C2PULSE) $(PAL_OPTS) --outdir $(OUT_DIR) $(C_FILES)
	@touch $@

# A negative test carries a `should-fail` file: verification must fail, and
# every line of that file must appear in the output. Without the second half a
# test could start failing for some unrelated reason and still look like it was
# doing its job. Standalone cases can instead carry `<case>.should-fail`.
ifneq ($(wildcard $(SHOULD_FAIL)),)
verify: $(OUT_DIR)/.stamp
	@if ! grep -q '[^[:space:]]' "$(SHOULD_FAIL)"; then \
		echo "ERROR: $(SHOULD_FAIL) must name an expected diagnostic" >&2; \
		exit 1; \
	fi; \
	if $(MAKE) --no-print-directory -f ../verify.mk \
		OUT_DIR=$(OUT_DIR) FSTAR_EXE="$(FSTAR_EXE)" CACHE_DIR=$(CACHE_DIR) \
		HELPERS=$(HELPERS) >$(OUT_DIR)/verify.log 2>&1; then \
		echo "ERROR: $(CURDIR) verified, but $(SHOULD_FAIL) says it must not" >&2; \
		exit 1; \
	fi; \
	while IFS= read -r pat || [ -n "$$pat" ]; do \
		[ -z "$$pat" ] && continue; \
		if ! grep -qF -- "$$pat" $(OUT_DIR)/verify.log; then \
			echo "ERROR: $(CURDIR) failed, but not for the expected reason:" >&2; \
			echo "       no line of the output contains '$$pat'" >&2; \
			exit 1; \
		fi; \
	done < "$(SHOULD_FAIL)"; \
	echo "Failed as expected: $(CURDIR)"
else
verify: $(OUT_DIR)/.stamp
	@$(MAKE) --no-print-directory -f ../verify.mk \
		OUT_DIR=$(OUT_DIR) FSTAR_EXE="$(FSTAR_EXE)" CACHE_DIR=$(CACHE_DIR) \
		HELPERS=$(HELPERS)
endif

compile: $(patsubst %.c,$(OBJ_DIR)/%.o,$(C_FILES))

$(OBJ_DIR)/%.o: %.c $(C_FILES) $(H_FILES)
	@mkdir -p $(OBJ_DIR)
	$(CC) $(INCLUDES) $(EXTRA_OPTS) -c $< -o $@

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR) $(OBJ_DIR) .depend

endif
