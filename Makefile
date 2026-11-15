LAKE ?= $(HOME)/.elan/bin/lake

.PHONY: all lean notes serve clean

all: lean notes

lean:
	cd lean && $(LAKE) build

notes:
	cd notes && $(LAKE) exe notes

serve:
	cd notes && $(LAKE) exe verso-serve _out/html-multi

clean:
	cd lean && $(LAKE) clean
	cd notes && $(LAKE) clean
	rm -rf notes/_out
