# Run inside the dev shell: `nix develop -c make check`.

.PHONY: build test format format-check proof-check check

build:
	lake build

test: build
	lake test

format:
	treefmt

format-check:
	treefmt --ci

proof-check:
	@status=0; grep -nErw --include='*.lean' 'sorry|admit' LeanClove LeanClove.lean LeanCloveTest.lean || status=$$?; \
	  if [ "$$status" -eq 0 ]; then echo "Proof placeholders are not allowed."; exit 1; fi; \
	  test "$$status" -eq 1

check: format-check proof-check test
