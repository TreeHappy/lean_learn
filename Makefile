LAKE ?= $(HOME)/.elan/bin/lake

.PHONY: all lean notes serve figures clean

all: lean notes

lean:
	cd lean && $(LAKE) build

# Regenerate the SVG figures in docs/figures from the Lean sources
# (Brane.Figures.*, rendered with the vendored Vizagrams library).
figures:
	cd lean && $(LAKE) exe gen-figures

notes:
	cd notes && $(LAKE) exe notes

serve:
	cd notes && $(LAKE) exe verso-serve _out/html-multi

clean:
	cd lean && $(LAKE) clean
	cd notes && $(LAKE) clean
	rm -rf notes/_out
