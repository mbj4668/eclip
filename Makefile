PROJECT = eclip
PROJECT_DESCRIPTION = Erlang library for command line parsing
PROJECT_VERSION = 1.0.0

TEST_DEPS = lux

include $(if $(ERLANG_MK_FILENAME),$(ERLANG_MK_FILENAME),erlang.mk)

all :: doc/eclip.md

doc/eclip.md: src/eclip.erl
	tools/gen-md.sh $< > $@

tests ::
	$(MAKE) lux

.PHONY: lux
lux:
	deps/lux/bin/lux test

clean ::
	rm -rf lux_logs
