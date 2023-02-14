# The `eclip` module

Eclip is a command line parser for Erlang programs.

## Types
### <a name="type_cmd">cmd()</a>

Specifies the main command and subcommands.
<pre><code>-type <a href="#type_cmd">cmd()</a> ::
        #{
          <span style="color:indianred">%% `name` is used as an identifier in the parse result.</span>
          <span style="color:indianred">%% If no `name` is given, the default is the `cmd` as an atom,</span>
          <span style="color:indianred">%% with dashes replaced with underscores.</span>
          name => atom(),

          <span style="color:indianred">%% `cmd` is the string that the user uses to invoke the</span>
          <span style="color:indianred">%% command.  It is required for subcommands.  The default</span>
          <span style="color:indianred">%% for the main command is the programname ("argv[0]").</span>
          cmd => string(),

          opts => [<a href="#type_opt">opt()</a> | <a href="#type_optgroup">optgroup()</a>],

          <span style="color:indianred">%% `args` specifies the positional arguments to the command.</span>
          <span style="color:indianred">%% `args` and `cmds` are mutually exclusive.</span>
          args => [<a href="#type_arg">arg()</a>],

          <span style="color:indianred">%% `cmds` specifies the subcommands to the command.</span>
          cmds => [<a href="#type_cmd">cmd()</a> | <a href="#type_cmdgroup">cmdgroup()</a>],

          <span style="color:indianred">%% `require_cmd` can only be set if `cmds` is set.  It means that</span>
          <span style="color:indianred">%% the user must give a subcommand (or an eager option).</span>
          require_cmd => boolean(),

          <span style="color:indianred">%% The string that is printed in the help text.  If set to</span>
          <span style="color:indianred">%% `hidden`, the command will not be displayed in the help</span>
          <span style="color:indianred">%% text.</span>
          help => string() | hidden,

          <span style="color:indianred">%% The string that is printed in the listing of subcommands.</span>
          <span style="color:indianred">%% Default is the first sentence of `help`.</span>
          short_help => string(),

          <span style="color:indianred">%% If a callback is given, it must have arity</span>
          <span style="color:indianred">%% 1 or arity 2 + number of options + number of arguments.</span>
          <span style="color:indianred">%% The first parameter is <a href="#type_parse_env">parse_env()</a> (where <a href="#type_cmd">cmd()</a> is the</span>
          <span style="color:indianred">%% spec for this cmd).</span>
          <span style="color:indianred">%% The second parameter is <a href="#type_result_cmd_stack">result_cmd_stack()</a>, i.e., the result of</span>
          <span style="color:indianred">%% parsing all ancestor commands.</span>
          <span style="color:indianred">%% Then follows each option value, and then each argument value.</span>
          cb => fun(({<a href="#type_parse_env">parse_env()</a>, <a href="#type_result_cmd_stack">result_cmd_stack()</a>,
                      <a href="#type_result_opts">result_opts()</a>, <a href="#type_result_args">result_args()</a>}) -> term()) |
                fun(),

          <span style="color:indianred">%% If `auto_help` is `false`, -h|--help isn't automatically</span>
          <span style="color:indianred">%% prepended to `opts`.</span>
          auto_help => boolean() <span style="color:indianred">% default true</span>
         }.
</code></pre>

### <a name="type_cmdgroup">cmdgroup()</a>

Used solely to group related commands in the help text.
<pre><code>-type <a href="#type_cmdgroup">cmdgroup()</a> ::
        {group, Header :: string(), [<a href="#type_cmd">cmd()</a>]}.
</code></pre>

### <a name="type_opt">opt()</a>

Specifies an option to a command.

An option is either `short` (on the form "-X") or `long` (on the
form "--XXX"), or both.  At least one of `short` and `long` must be
specified.

By default, an option is optional, but can be declared as `required`.

An option can be given once or multiple times (controlled with
the `multiple` field).

An option either has no arguments, one argument (simple case), or
multiple, but a fixed number of, arguments (complex case).  This is
controlled by specifying a `type` or `args`.

If the option has no arguments, or a single argument, `type` is used.
Otherwise `args` is used.  `type` and `args` are mutually exclusive.

If neither `type` nor `args` is specified, and no `default` is set,
`type` defaults to `string`.  If `default` is set, `type` is deduced
from the default value.

When the parser parses zero, one or several options, the resulting
erlang term depends on the `type`, `args, `default` and `multiple`
fields.
<pre><code>-type <a href="#type_opt">opt()</a> ::
        #{
          <span style="color:indianred">%% `name` is used as as an identifier in the parse result</span>
          <span style="color:indianred">%% If no `name` is given, the default is the long option (if</span>
          <span style="color:indianred">%% given) as an atom with dashes replaced with underscores,</span>
          <span style="color:indianred">%% or otherwise the short option as an atom.</span>
          name => atom(),

          <span style="color:indianred">%% At least one of `short` and `long` must be given.</span>
          short => char(),
          long => string(),

          <span style="color:indianred">%% The string that is printed in the help text.  If set to</span>
          <span style="color:indianred">%% `hidden`, the command will not be displayed in the help</span>
          <span style="color:indianred">%% text.</span>
          help => string() | hidden,

          <span style="color:indianred">%% If `multiple` is given, val will either be a list of each</span>
          <span style="color:indianred">%% value, or - if `type` is `count` - an integer.</span>
          multiple => boolean(),

          type => flag       <span style="color:indianred">% val is 'true'</span>
                | boolean    <span style="color:indianred">% --no-<long> is used to disable, val is boolean()</span>
                | count      <span style="color:indianred">% implies `multiple`, val is integer()</span>
                | <a href="#type_argtype">argtype()</a>  <span style="color:indianred">% val is <a href="#type_argval">argval()</a></span>
                | <a href="#type_arg">arg()</a>,     <span style="color:indianred">% val is <a href="#type_argval">argval()</a></span>

          <span style="color:indianred">%% each arg in `args` must have an integer-valued `nargs`, or</span>
          <span style="color:indianred">%% `nargs => '?'`</span>
          args => [<a href="#type_arg">arg()</a>],   <span style="color:indianred">% val is <a href="#type_result_args">result_args()</a></span>

          default => term(), <span style="color:indianred">% val is default if not given</span>

          <span style="color:indianred">%% Default is `name` in uppercase or in brackets (depending</span>
          <span style="color:indianred">%% on `metavar_style` in `<a href="#type_parse_opts">parse_opts()</a>).  Only used if `type`</span>
          <span style="color:indianred">%% is an <a href="#type_argtype">argtype()</a>.</span>
          metavar => string(),

          required => boolean(), <span style="color:indianred">% default is `false`</span>

          expose_value => boolean(), <span style="color:indianred">% default is `true`</span>

          <span style="color:indianred">%% If the option is found, the callback is invoked.  The callback</span>
          <span style="color:indianred">%% can throw `{done, term()}` to stop parsing.  This is useful</span>
          <span style="color:indianred">%% e.g., to implement `--version` or `--help`.</span>
          cb => fun((<a href="#type_parse_env">parse_env()</a>, <a href="#type_result_opts">result_opts()</a>) -> <a href="#type_result_opts">result_opts()</a>)
          }.
</code></pre>

### <a name="type_optgroup">optgroup()</a>

Used solely to group related options in the help text.
<pre><code>-type <a href="#type_optgroup">optgroup()</a> ::
        {group, Header :: string(), [<a href="#type_opt">opt()</a>]}.
</code></pre>

### <a name="type_arg">arg()</a>

Specifies a positional argument to a command or option.

An argument has a field `nargs` which specifies how many times the
argument can be given.
<pre><code>-type <a href="#type_arg">arg()</a> ::
        #{
          <span style="color:indianred">%% `name` is used as as an identifier in the parse result.</span>
          name := atom(),

          <span style="color:indianred">%% Default is `name` in uppercase or in brackets (depending</span>
          <span style="color:indianred">%% on `metavar_style` in `<a href="#type_parse_opts">parse_opts()</a>).</span>
          metavar => string(),

          type => <a href="#type_argtype">argtype()</a>,

          <span style="color:indianred">%% `nargs` specifies how many arguments can be given.</span>
          <span style="color:indianred">%%   '?' means zero or one</span>
          <span style="color:indianred">%%   '*' means zero or more</span>
          <span style="color:indianred">%%   '+' means one or more</span>
          <span style="color:indianred">%%    N  means exactly N</span>
          <span style="color:indianred">%% only the last arg can have nargs '*' or '+'.</span>
          <span style="color:indianred">%% if one arg has nargs '?', the following args must also have</span>
          <span style="color:indianred">%% nargs '?'.</span>
          <span style="color:indianred">%% default is 1</span>
          nargs => pos_integer() | '?' | '*' | '+',

          default => term()
         }.
</code></pre>

### <a name="type_argtype">argtype()</a>

<pre><code>-type <a href="#type_argtype">argtype()</a> ::
        <span style="color:indianred">%% Any string</span>
        string
        <span style="color:indianred">%% A string that matches all of the given regexps</span>
      | {string, [Regexp :: string()]}
        <span style="color:indianred">%% One of the given strings</span>
      | {enum, [atom()]}
        <span style="color:indianred">%% any float</span>
      | float
        <span style="color:indianred">%% A float that falls into one of the given ranges</span>
      | {float, [range(float())]}
        <span style="color:indianred">%% Any integer</span>
      | integer
        <span style="color:indianred">%% An integer that falls into one of the given ranges</span>
      | {integer, [range(integer())]}
        <span style="color:indianred">%% Any term</span>
      | {custom, fun((string()) -> {ok, term()} | {error, Msg :: string()})}
      .
</code></pre>

### <a name="type_parse_result">parse_result()</a>

<pre><code>-type <a href="#type_parse_result">parse_result()</a> ::
        {<span style="color:indianred">%% The name of the selected command or subcommand.</span>
         CmdName :: atom(),

         <span style="color:indianred">%% The options given to `CmdName`.</span>
         Opts :: <a href="#type_result_opts">result_opts()</a>,

         <span style="color:indianred">%% The positional arguments given to `CmdName`.</span>
         Args :: <a href="#type_result_args">result_args()</a>,

         <span style="color:indianred">%% If `CmdName` is a subcommand, `CmdStack` contains the</span>
         <span style="color:indianred">%% selected ancestor commands and the options given to them.</span>
         CmdStack :: <a href="#type_result_cmd_stack">result_cmd_stack()</a>}.
</code></pre>

### <a name="type_result_opts">result_opts()</a>

<pre><code>-type <a href="#type_result_opts">result_opts()</a> ::
        #{OptName :: atom() => integer()     <span style="color:indianred">% if type is count</span>
                             | <a href="#type_optval">optval()</a>      <span style="color:indianred">% else if multiple is false</span>
                             | [<a href="#type_optval">optval()</a>]    <span style="color:indianred">% else multiple is true</span>
         }.
</code></pre>

### <a name="type_result_args">result_args()</a>

<pre><code>-type <a href="#type_result_args">result_args()</a> ::
        #{ArgName :: atom() => <a href="#type_argval">argval()</a>      <span style="color:indianred">% if nargs is '?' or 1</span>
                             | [<a href="#type_argval">argval()</a>]    <span style="color:indianred">% if nargs > 1 or '*' or '+'</span>
         }.
</code></pre>

### <a name="type_result_cmd_stack">result_cmd_stack()</a>

<pre><code>-type <a href="#type_result_cmd_stack">result_cmd_stack()</a> ::
        [{CmdName :: atom(),
          Opts :: <a href="#type_result_opts">result_opts()</a>}].
</code></pre>

### <a name="type_optval">optval()</a>

<pre><code>-type <a href="#type_optval">optval()</a> ::
        'true'        <span style="color:indianred">% if type is 'flag'</span>
      | boolean()     <span style="color:indianred">% if type is 'boolean'</span>
      | <a href="#type_argval">argval()</a>      <span style="color:indianred">% if type is an <a href="#type_argtype">argtype()</a></span>
      | <a href="#type_result_args">result_args()</a> <span style="color:indianred">% if args is set</span>
      .
</code></pre>

### <a name="type_argval">argval()</a>

<pre><code>-type <a href="#type_argval">argval()</a> ::
        string()   <span style="color:indianred">% if argtype is 'string'</span>
      | atom()     <span style="color:indianred">% if argtype is 'enum'</span>
      | integer()  <span style="color:indianred">% if argtype is 'integer'</span>
      | float()    <span style="color:indianred">% if argtype is 'float'</span>
      | term()     <span style="color:indianred">% if argtype is 'custom'</span>
      .
</code></pre>

### <a name="type_parse_opts">parse_opts()</a>

<pre><code>-type <a href="#type_parse_opts">parse_opts()</a> ::
        #{
          <span style="color:indianred">%% caps:           `name` as all-caps, with `-` replaced with `_`</span>
          <span style="color:indianred">%% angle_brackets: `name` surrounded by angle brackets</span>
          metavar_style => caps | angle_brackets,

          <span style="color:indianred">%% If `version` is given, the option `--version` is automatically</span>
          <span style="color:indianred">%% added to the main command.</span>
          version => string(),

          <span style="color:indianred">%% If `default_help_opt` is set to `true`, `-h|--help` is added to</span>
          <span style="color:indianred">%% the command and all subcommands.</span>
          default_help_opt => boolean(), <span style="color:indianred">% default is 'true'</span>

          <span style="color:indianred">%% If `print_usage_on_error` is set to 'true', a message will</span>
          <span style="color:indianred">%% be printed to stderr if parsing of the command line failed.</span>
          print_usage_on_error => boolean(), <span style="color:indianred">% default is 'true'</span>

          <span style="color:indianred">%% A user-defined term.  Useful to pass data to callbacks.</span>
          user => term()
         }.
</code></pre>

### <a name="type_parse_env">parse_env()</a>

<pre><code>-type <a href="#type_parse_env">parse_env()</a> :: {<a href="#type_cmd">cmd()</a>, <a href="#type_parse_opts">parse_opts()</a>}.
</code></pre>

## Functions
### <a name="func_parse">parse/2</a>

<pre><code>-spec parse(CmdLine :: [string()],
            CmdSpec :: <a href="#type_cmd">cmd()</a>) ->
    {done, term()}
  | {ok, <a href="#type_parse_result">parse_result()</a>}
  | {error, Error :: term()}
  | CbRes :: term()
  .
</code></pre>
Equivalent to `parse(CmdLine, CmdSpec, #{})`.

### <a name="func_parse">parse/3</a>

<pre><code>-spec parse(CmdLine :: [string()],
            CmdSpec :: <a href="#type_cmd">cmd()</a>,
            Options :: <a href="#type_parse_opts">parse_opts()</a>) ->
    {done, term()}
  | {ok, <a href="#type_parse_result">parse_result()</a>}
  | {error, Error :: term()}
  | CbRes :: term()
  .
</code></pre>
Parse a command line of strings according to the `CmdSpec`.

If parsing fails, a message is printed to the user, and
`{error, term()}` is returned.  The message can be suppressed with
the parse option `print_usage_on_error => false`.

If the selected command (main or subcommand) has a callback defined,
the return value from the callback is returned, unless it returns
`{error, ErrMsg :: iodata(), Reason :: term()}`, in which case
parsing fails and `ErrMsg` is printed to the user (see above), and
`<a href="#type_parse">parse()</a>` returns `{error, Reason}`.

If any option's callback throws `{done, term()}`, this is returned.

Otherwise, parsing succeeds and no callback was invoked, the
`parse` function returns `{ok, <a href="#type_parse_result">parse_result()</a>}`.



### <a name="func_default_help_opt">default_help_opt/0</a>

<pre><code>-spec <a href="#type_default_help_opt">default_help_opt()</a> -> <a href="#type_opt">opt()</a>.
</code></pre>
Returns the option spec for `-h|--help`.

### <a name="func_default_version_opt">default_version_opt/0</a>

<pre><code>-spec <a href="#type_default_version_opt">default_version_opt()</a> -> <a href="#type_opt">opt()</a>.
</code></pre>
Returns the option spec for `--version`.

