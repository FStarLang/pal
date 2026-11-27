.PHONY: all check-template check-exit-status clean

C2PULSE ?= ../target/debug/pal

TESTS := $(shell find . -mindepth 1 -maxdepth 1 -type d \
	! -name '_*' ! -name '.*' | sort | sed 's|^\./||')

all: check-template check-exit-status $(TESTS)

check-template:
	@./check-template.sh

check-exit-status:
	@python3 ./check-exit-status.py "$(abspath $(C2PULSE))"

.PHONY: $(TESTS)
$(TESTS):
	@$(MAKE) -C $@

clean:
	@for d in $(TESTS); do $(MAKE) -C $$d clean; done
