.PHONY: all check-template clean

TESTS := $(shell find . -mindepth 1 -maxdepth 1 -type d \
	! -name '_*' ! -name '.*' | sort | sed 's|^\./||')

all: check-template $(TESTS)

check-template:
	@./check-template.sh

.PHONY: $(TESTS)
$(TESTS):
	@echo "=== $@ ==="
	@$(MAKE) -C $@

clean:
	@for d in $(TESTS); do $(MAKE) -C $$d clean; done
