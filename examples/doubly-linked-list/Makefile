.DEFAULT_GOAL := all
.DELETE_ON_ERROR:

ROOT := ../..
PAL := $(ROOT)/target/debug/pal
ANNOTATIONS := $(ROOT)/target/debug/pal_annotations
FSTAR_EXE ?= $(abspath $(ROOT)/opt/run-fstar.sh)
BUILD := _build
CFLAGS ?= -std=c11 -O2 -Wall -Wextra
SOURCES := dll.c client.c

.PHONY: all tools prepare translate verify native check-overlay clean
all: verify native check-overlay

# The repository's test target has already built these prerequisites.
tools:
ifneq ($(TOOLCHAIN_READY),1)
	+$(MAKE) -C $(ROOT) all
endif

$(PAL) $(ANNOTATIONS): | tools
	@test -x $@

prepare: $(BUILD)/annotated/.stamp

$(BUILD)/annotated/.stamp: $(SOURCES) dll.h pal.h proofs.annotations $(ANNOTATIONS) | tools
	@mkdir -p $(BUILD)/annotated
	cp $(SOURCES) dll.h pal.h $(BUILD)/annotated/
	$(ANNOTATIONS) --root $(BUILD)/annotated --apply proofs.annotations --check
	$(ANNOTATIONS) --root $(BUILD)/annotated --apply proofs.annotations
	@touch $@

translate: $(BUILD)/out/.stamp

$(BUILD)/out/.stamp: $(BUILD)/annotated/.stamp $(PAL)
	rm -rf _build/out
	@mkdir -p $(BUILD)/out
	$(PAL) --outdir $(BUILD)/out $(addprefix $(BUILD)/annotated/,$(SOURCES))
	@touch $@

verify: translate
	+$(MAKE) -f verify.mk FSTAR_EXE="$(FSTAR_EXE)"

native: $(BUILD)/native-check $(BUILD)/native-check-ndebug
	$(BUILD)/native-check
	$(BUILD)/native-check-ndebug

$(BUILD)/native-check: $(SOURCES) native-check.c dll.h pal.h
	@mkdir -p $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SOURCES) native-check.c $(LDFLAGS) -o $@

$(BUILD)/native-check-ndebug: $(SOURCES) native-check.c dll.h pal.h
	@mkdir -p $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -DNDEBUG $(SOURCES) native-check.c $(LDFLAGS) -o $@

# Work on copies: extraction must neither consume dll.h's contracts nor alter
# the checked-in C files. A second apply must be a no-op.
check-overlay: prepare
	python3 check-overlay.py "$(abspath $(ANNOTATIONS))"

clean:
	rm -rf _build
