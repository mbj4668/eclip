BUILD_DEPS = erl_md

dep_erl_md = git https://github.com/mbj4668/erl_md

include erl.mk

erl.mk:
	curl -s -O https://raw.githubusercontent.com/mbj4668/erl.mk/main/$@

all: doc/eclip.md

doc/eclip.md: src/eclip.erl
	$(DEPS_DIR)/erl_md/gen-md.sh $< > $@
