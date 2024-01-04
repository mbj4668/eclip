include erl.mk

erl.mk:
	curl -O https://raw.githubusercontent.com/mbj4668/erl.mk/main/$@

all: doc/eclip.md

doc/eclip.md: src/eclip.erl
	tools/gen-md.sh $< > $@
