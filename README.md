# Eclip - Erlang library for command line parsing

Eclip is a command line parser for Erlang programs.  It is similar in
functionality to Python's `click`.

The erlang module is called `eclip` and is documented in
[eclip.md](doc/eclip.md).

Here's an example of a simple script:

```erlang
#!/usr/bin/env escript
-mode(compile).

main(Args) ->
    eclip:parse(Args, spec(), #{}).

spec() ->
    #{help => "Simple program that greets NAME for a total of COUNT times.",
      opts => [#{long => "name", required => true,
                 help => "The person to greet"},
               #{long => "count", default => 1,
                 help => "Number of greetings"}],
      cb => fun hello/4}.

hello(_, _, Name, Count) ->
    lists:foreach(
      fun(_) -> io:format("Hello ~s!\n", [Name]) end,
      lists:seq(1, Count)).
```

It looks likes this when it is run:

```shell-session
$ hello  --name Martin --count 3
Hello Martin!
Hello Martin!
Hello Martin!
```

Eclip automatically generates nice help text:

```shell-session
$ hello --help
Usage: ./hello [OPTIONS]

  Simple program that greets NAME for a total of COUNT times.

Options:
  -h, --help                 Show this help and exit
      --completion [SHELL]   Print sourceable bash/zsh completion script. If no
                             parameter is given, a guess will be made based on
                             $SHELL.
      --name NAME            The person to greet
      --count COUNT          Number of greetings
```

And it automatically generates shell completion scripts:

```shell-session
$ source <(./hello --completion)
$ hello --n<tab>
$ hello --name
```


## Design goals / features

  -  Simple to use for the programmer (specify as little as possible)
  -  Short and long options, with or without arguments
     (e.g., `--force -p 2 3`)
  -  Positional arguments
  -  Hierarchical subcommands
  -  Validation of argument values
  -  Autogenerated help, also for subcommands
  -  Option groups in help
  -  Command groups in help
  -  Clear distinction of `command`, `option`, and `argument`
  -  Opinionated, but _some_ customization support
  -  Autogenerated completion for bash/zsh

### Stretch goals / later

  -  Mutually exclusive options
  -  Generation of man pages

### Non-goals

  -  Support for variations of the command line syntax above
     (e.g., "+" or "/" instead of "-" for an option; or long options
     prefixed with a single "-"; or using "=" to set an option).
  -  Support for abbreviated given long options
     (e.g., "--read-full-rec" instead of "--read-full-records")


# Command line syntax

Three ways of describing the command line syntax supported by the
parser:

### Plain text

A _command_ has a set of _options_, followed by a list of _arguments_
or a _(sub)command_ (which in turn has options and arguments or
subcommands).

An option has a name, followed by a list of arguments.

### Pseudo-spec

```
  COMMAND [OPTIONS] [--] [ARGUMENTS]
  COMMAND [OPTIONS] [SUBCOMMAND [OPTIONS] [--] [ARGUMENTS]]
  COMMAND [OPTIONS] [SUBCOMMAND [OPTIONS] [SUBSUBCOMMAND ...]]
```

### ABNF grammar of a command line

```
  command-line = command [WSP parameters]
  command      = 1*CHAR
  parameters   = options [WSP (["--" WSP] arguments) / command-line]

  options      = option *(WSP option)
  option       = (short-opt / long-opt) [arguments]
  short-opt    = "-" CHAR
                     / 2*CHAR ; multiple short opts at the same time
  long-opt     = "--" 1*CHAR

  arguments    = argument *(WSP argument)
  argument     = 1*CHAR

  WSP  = < whitespace >
  CHAR = < printable unicode character >
```

## Options

There are two styles of options supported; short and long.

### Short options

In short-option style, each option letter is prefixed with a single
dash.  If a short option takes an argument, the argument follows as
a separate command line word.

Any number of short options not taking arguments can be clustered
together after a single dash, e.g., `-vkp` is equivalent to `-v -k
-p`.  Options that take arguments can appear at the end of such a
cluster, e.g., `-vkpf foo.txt`.

Note that the legacy style of passing an argument to a short option
without separating whitespace is not supported.

See https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap12.html#tag_12_02.


### Long options

In long-option style, each option begins with two dashes and has a
meaningful name, usually consisting of lower-case letters and dashes
(this is not enforced).  If a long option takes an argument, the
argument follows as a separate command line word.

Note that abbreviated long options are not supported.

Also note that passing an argument to a long option by separating it
with an equal sign instead of whitespace is not supported.



# Examples

### Option with one argument

The command takes one option, specified as `-l` or `--label`.  The
option requires a label (string) as argument.


```erlang
%% mycmd --label foo
parse(["--label", "foo"],
      #{cmd => "mycmd",
        opts => [#{name => label, short => $l, long => "label",
                  type => string}]}, #{}).

> {ok, {mycmd, #{label => "foo"}, #{}, []}}
```

The default `type` is `string`, and the default `name` is the long
option as an atom, so the above can also be written as:

```erlang
%% mycmd --label foo
parse(["--label", "foo"],
      #{cmd => "mycmd",
        opts => [#{short => $l, long => "label"}]}).

> {ok, {mycmd, #{label => "foo"}, #{}, []}}
```

### Flag option

The command has one option with no argument.
If no `name` and no `long` option is given, the `name` defaults to the
short option as an atom.

```erlang
%% mycmd -s
parse(["-s"],
      #{cmd => "mycmd",
        opts => [#{short => $s, type => flag}]}).

> {ok, {mycmd, #{s => true}, #{}, []}}
```

We can also give the option a better name.

```erlang
%% mycmd
parse([],
      #{cmd => "mycmd",
        opts => [#{name => silent, short => $s, type => flag}]}).

> {ok, {mycmd, #{silent => false}, #{}, []}}
```

### Count option

The command has an option `-v` which can be given mulitple times to
increase the verbosity.

```erlang
%% mycmd -vvv -v
parse(["-vvv", "-v"],
      #{cmd => "mycmd",
        opts => [#{name => verbosity, short => $v, type => count}]}).

> {ok, {mycmd, #{verbosity => 4}, #{}, []}}
```


### Option with one argument, and one argument to the command

```erlang
%% mycmd -l foo log.txt
parse(["-l", "foo", "log.txt"],
      #{cmd => "mycmd",
        opts => [#{name => label, short => $l, type => string}],
        args => [#{name => filename}]}).


> {ok, {mycmd, #{label => "foo"}, #{filename => "log.txt"}, []}}
```
### Option with two arguments

The command should have an option `--user` that takes a required
`name`, and an optional `id` argument.  For this, we cannot use the
simple `type` field, but must use the more generic and flexible `args`
instead.

```erlang
%% mycmd --user joe 42
parse(["--user", "joe", "42"],
      #{cmd => "mycmd",
        opts => [#{name => user, long => "user",
                   args => [#{name => name, type => string},
                            #{name => id, type => integer, nargs => '?'}]}]}).

> {ok, {mycmd, #{user => #{id => 42, name => "joe"}}, #{}, []}
```

### Command with variable number of arguments

The command should take a possibly empty list of files as arguments.

```erlang
%% mycmd foo.txt bar.txt
parse(["foo.txt", "bar.txt"],
      #{cmd => "mycmd",
        args => [#{name => filename, type => string, nargs => '*'}]}).

> {ok, {mycmd, #{}, #{filename => ["foo.txt","bar.txt"]}, []}}
```

### Callbacks

If a callback is given, it must either have arity `1` or `2 + number of options +
number of arguments`.  For example, the `list` command below has two
options and one argument, so the arity can be 5:

```erlang
%% mycmd -v list --foo bar.txt
parse(["-v", "list", "--foo", "bar.txt"],
      #{cmd => "mycmd",
        opts => [#{name => verbosity, short => $v, type => count}],
        cmds => [#{cmd => "list",
                   opts => [#{long => "foo", type => boolean},
                            #{long => "bar", type => boolean}],
                   args => [#{name => filename}],
                   cb => fun do_list/5}]}).

do_list(ParseEnv, CmdStack, Foo, Bar, Filename) ->
    io:format("Stack = ~p\nFoo = ~p\nBar = ~p\nFilename = ~s\n",
              [CmdStack, Foo, Bar, Filename]).

% results in:

Stack = [{mycmd, #{verbosity => 1}}]
Foo = true
Bar = false
Filename = "bar.txt"
```

Alternatively, the arity can be 1, in which case it will be invoked
as:

```erlang
do_list([_ParseEnv,
         [{mycmd,#{verbose => 1}}],
         #{bar => false,foo => true},
         #{filename => "bar.txt"}]).
```

### Command with subcommands

The following example implements a basic calculator, and demonstrates
a command with two levels of subcommands:

```erlang
#!/usr/bin/env escript
%% -*- erlang -*-
%%! -pa ../ebin

-mode(compile).

main(Args) ->
    case eclip:parse(Args, spec(), #{}) of
        {done, _} ->
            ok;
        R ->
            io:format("~p\n", [R])
    end.

spec() ->
    #{cmds =>
          [#{cmd => "sum",
             args => [#{name => term, type => int, nargs => '+'}],
             cb => fun(_, _, Terms) -> lists:sum(Terms) end},
           #{cmd => "div",
             args => [#{name => denominator, type => float},
                      #{name => numerator, type => float}],
             cb => fun(_, _, D, N) -> D / N end},
           #{cmd => "math",
             cmds =>
                 [#{cmd => "sin",
                    args => [#{name => num, type => float}],
                    cb => fun do_sin/3},
                  #{cmd => "cos",
                    args => [#{name => num, type => float}],
                    cb => fun do_cos/3},
                  #{cmd => "tan",
                    args => [#{name => num, type => float}],
                    cb => fun do_tan/3}]}]}.

do_sin(_, _, Num) ->
    math:sin(Num).

do_cos(_, _, Num) ->
    math:cos(Num).

do_tan(_, _, Num) ->
    math:tan(Num).
```

The calculator provides a `sum` command that prints a sum of integer
numbers:

```shell-session
$ ./calc sum 1 2 3
6
```

Math subcommands provide trigonometric functions:

```shell-session
$ ./calc math cos 1.2
0.3623577544766736
$ ./calc math sin 1
0.8414709848078965
```

### Shell completion

We can enable completion for the previous example command.

In Bash:

```shell-session
$ source <(./calc --completion)
$ ./calc <tab><tab>
div           sum           --help
math          --completion  -h
$ ./calc m<tab>
$ ./calc math <tab><tab>
cos     sin     tan     --help  -h
```

In Zsh:

```shell-session

% source <(./calc --completion zsh)
% ./calc <tab>
div           sum           --help
math          --completion  -h
$ ./calc m<tab>
$ ./calc math <tab>
cos     sin     tan     --help  -h
```


# Related work

- getopt - (various); very simple, no support for command hierarchies.
- erlang-cli - good docs; no support for command hierarchies.
- argparse - doesn't handle subcommands as truly separate commands,
               e.g. doesn't allow `cmd -f subcmd -f`;
             chatty syntax;
             doens't handle option / command groups
             no completion
