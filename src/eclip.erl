%%% Eclip is a command line parser for Erlang programs.
%%%
-module(eclip).

-export([parse/2, parse/3]).
-export([fmt_help/2, fmt_help/3, print_help/2, print_help/3]).

-export([default_help_opt/0,
         default_version_opt/0,
         default_completion_opt/0]).

-export_type([cmd/0, cmdgroup/0,
              opt/0, optgroup/0,
              arg/0, argtype/0, range/1,

              cmd_cb/0, cmd_cb_res/0,

              parse_result/0,
              result_opts/0, result_args/0, cmd_stack/0,
              optval/0, argval/0,
              parse_opts/0, parse_env/0,

              doc/0, p/0, ul/0, dl/0, pre/0]).

-define(iof, io:format).
-define(a2l, atom_to_list).
-define(l2a, list_to_atom).

-define(iolf, io_lib:format).
-define(nl, io_lib:nl()).

%% Specifies the main command and subcommands.
-type cmd() ::
        #{
          %% `name` is used as an identifier in the parse result.
          %% If no `name` is given, the default is the `cmd` as an atom,
          %% with dashes replaced with underscores.
          name => atom(),

          %% `cmd` is the string that the user uses to invoke the
          %% command.  It is required for subcommands.  The default
          %% for the main command is the program name ("argv[0]").
          cmd => string(),

          %% `opts` specifies the options to the command.
          opts => [opt() | optgroup()],

          %% `args` specifies the positional arguments to the command.
          %% `args` and `cmds` are mutually exclusive.
          args => [arg()],

          %% `cmds` specifies the subcommands to the command.
          cmds => [cmd() | cmdgroup()],

          %% `require_cmd` can only be set if `cmds` is set.  It means that
          %% the user must give a subcommand (or an eager option).
          require_cmd => boolean(),

          %% The string that is printed in the help text.  If set to
          %% `hidden`, the command will not be displayed in the help
          %% text.  Use two consecutive newlines to break the text
          %% into paragraphs. For more complex help formatting, use `doc()`.
          help => string() | doc() | hidden,

          %% The string that is printed in the listing of subcommands.
          %% Default is the first sentence of `help`.
          short_help => string(),

          %% Optional callback that implements the command or subcommand.
          cb => cmd_cb()
         }.
%% Used solely to group related commands in the help text.
-type cmdgroup() ::
        {group, Header :: string(), [cmd()]}.

%% Specifies an option to a command.
%%
%% An option is either `short` (on the form "-X") or `long` (on the
%% form "--XXX"), or both.  At least one of `short` and `long` must be
%% specified.
%%
%% By default, an option is optional, but can be declared as `required`.
%%
%% An option can be given once or multiple times (controlled with
%% the `multiple` field).
%%
%% An option either has no arguments, one argument (simple case), or
%% multiple, but a fixed number of, arguments (complex case).  This is
%% controlled by specifying a `type` or `args`.
%%
%% If the option has no arguments, or a single argument, `type` is used.
%% Otherwise `args` is used.  `type` and `args` are mutually exclusive.
%%
%% If neither `type` nor `args` is specified, and no `default` is set,
%% `type` defaults to `string`.  If `default` is set, `type` is deduced
%% from the default value.
%%
%% When the parser parses zero, one or several options, the resulting
%% erlang term depends on the `type`, `args, `default` and `multiple`
%% fields.
%%
%% In the parse result, each given option, and all options with default
%% values are collected into a map `result_opts()`, which maps the option's
%% `name` to an `optval()`.
-type opt() ::
        #{
          %% `name` is used as as an identifier in the parse result
          %% If no `name` is given, the default is the long option (if
          %% given) as an atom with dashes replaced with underscores,
          %% or otherwise the short option as an atom.
          name => atom(),

          %% At least one of `short` and `long` must be given.
          short => char(),
          long => string(),

          %% The string that is printed in the help text.  If set to
          %% `hidden`, the command will not be displayed in the help
          %% text.
          help => string() | hidden,

          %% If `multiple` is `true`, the option can be given multiple
          %% times, and the optval will either be a list of each
          %% value, or - if `type` is `count` - an integer.
          multiple => boolean(),

          %% The type of a single valued option argument.
          %% `type` and `args` are mutually exclusive.
          type => flag       % optval is 'true'
                | boolean    % --no-<long> to disable, optval is boolean()
                | count      % implies `multiple`, optval is integer()
                | argtype()  % optval is argval()
                | arg(),     % optval is argval()

          %% each arg in `args` must have an integer-valued `nargs`, or
          %% `nargs => '?'`
          args => [arg()],   % optval is result_args()

          default => term(), % optval is this term if the option is not given

          %% if `default_in_help` is `false`, the given default value is not
          %% automatically printed in the help string
          default_in_help => boolean(), % default is `true`

          %% if `enum_in_help` is `false`, and `type` is an enumeration,
          %% the enums are not automatically printed in the help string
          enum_in_help => boolean(), % default is `true`

          %% The name of the option in help text.
          %% Default is `name` in uppercase or in brackets (depending
          %% on `metavar_style` in `parse_opts()).  Only used if `type`
          %% is an argtype().
          metavar => string(),

          required => boolean(), % default is `false`

          %% If `expose_value` is `false`, then the option is not included
          %% in the arguments to callbacks with arity > 1.
          expose_value => boolean(), % default is `true`

          %% If the option is found, the callback is invoked.
          cb => opt_cb()
          }.
%% Used to define a set of mutually exclusive options.
%-type optchoice() ::
%        {choice, [[opt() | optchoice()]]}.
%% Used solely to group related options in the help text.
-type optgroup() ::
        {group, Header :: string(), [opt()]}.

%% Specifies a positional argument to a command or option.
%%
%% An argument has a field `nargs` which specifies how many times the
%% argument can be given.
%%
%% In the parse result, each given argument, and all arguments with
%% default values are collected into a map `result_args()`, which maps
%% the argument's `name` to an `argval()`.
-type arg() ::
        #{
          %% `name` is used as as an identifier in the parse result.
          name := atom(),

          %% Default is `name` in uppercase or in brackets (depending
          %% on `metavar_style` in `parse_opts()).
          metavar => string(),

          type => argtype(),

          %% `nargs` specifies how many arguments can be given.
          %%   '?' means zero or one
          %%   '*' means zero or more
          %%   '+' means one or more
          %%    N  means exactly N
          %% only the last arg can have nargs '*' or '+'.
          %% if one arg has nargs '?', the following args must also have
          %% nargs '?'.
          %% default is 1
          nargs => pos_integer() | '?' | '*' | '+',

          default => term() % argval is this term if the argument is not given
         }.

%% Specifies the type of an `arg()`.
-type argtype() ::
        %% A string that represents a directory (helps completion)
        dir
        %% A string that represents a filename (helps completion)
      | file
        %% Any string
      | string
        %% A string that matches all of the given regexps
      | {string, [Regexp :: string()]}
        %% One of the given strings
      | {enum, [atom()]}
        %% any float
      | float
        %% A float that falls into one of the given ranges
      | {float, [range(float())]}
        %% Any integer
      | int
        %% An integer that falls into one of the given ranges
      | {int, [range(integer())]}
        %% Any term
      | {custom, fun((string()) -> {ok, term()} | error)}
      .

%% Specifies a closed range, i.e., `Min` and `Max` are valid
%% values (when they are numbers).
-type range(T) :: T | {Min :: T | 'unbounded',
                       Max :: T | 'unbounded'}.

%% A callback function in a `cmd`.  It is invoked when a command or
%% subcommand is selected by the user.
%%
%% The callback must have arity 1 or arity 2 + number of options +
%% number of arguments.  The spec for arity 1 is given below in the type,
%% and for the other case, the function is called as:
%%
%% - The first parameter is `parse_env()` (where `cmd()` is the
%%   spec for this cmd).
%% - The second parameter is `cmd_stack()`, i.e., the result of
%%   parsing all ancestor commands.
%% - Then follows each option value, and then each argument value; these
%%   are `undefined` if not given or have defaults.
-type cmd_cb() ::
        fun((parse_result()) -> cmd_cb_res())
      | fun((...) -> cmd_cb_res()).

%% The return value of a callback defined in `cmd`.
%%
-type cmd_cb_res() ::
        Res :: term()
      | {error, ErrMsg :: string(), Error :: term()}.


%% A callback function in an `opt`.  It is invoked if the option is
%% given on the command line.
%%
%% The callback is called with the options gathered so far, and it
%% must either return new options (possibly modified), or stop
%% parsing by throwing `{done, term()}`.  This is useful
%% e.g., to implement `--version` or `--help`.  An option that
%% throws '{done, term()}' is called an eager option.
-type opt_cb() :: fun((parse_env(), result_opts(), cmd_stack()) ->
                             result_opts()).


%% The `parse_env()` contains the `cmd()` spec for the selected command
%% or subcommand, and the `parse_opts()` given to the `parse()` call.
-type parse_env() :: {cmd(), parse_opts()}.

-type parse_result() ::
        {%% The cmd() of the selected command or subcommand and parse_opts().
         Env :: parse_env(),

         %% If `CmdName` is a subcommand, `CmdStack` contains the
         %% selected ancestor commands and the options given to them.
         CmdStack :: cmd_stack(),

         %% The options given to `CmdName`.
         Opts :: result_opts(),

         %% The positional arguments given to `CmdName`.
         Args :: result_args()}.

-type result_opts() ::
        #{OptName :: atom() => integer()     % if type is count
                             | optval()      % else if multiple is false
                             | [optval()]    % else multiple is true
         }.

-type result_args() ::
        #{ArgName :: atom() => argval()      % if nargs is '?' or 1
                             | [argval()]    % if nargs > 1 or '*' or '+'
         }.

-type optval() ::
        'true'        % if type is 'flag'
      | boolean()     % if type is 'boolean'
      | argval()      % if type is an argtype()
      | result_args() % if args is set
      .

-type argval() ::
        string()   % if argtype is 'string', 'dir' or 'file'
      | atom()     % if argtype is 'enum'
      | integer()  % if argtype is 'int'
      | float()    % if argtype is 'float'
      | term()     % if argtype is 'custom'
      .

-type cmd_stack() ::
        [{cmd(),
          Opts :: result_opts()}].


-type parse_opts() ::
        #{
          %% caps:           `name` as all-caps, with `-` replaced with `_`
          %% angle_brackets: `name` surrounded by angle brackets
          metavar_style => caps | angle_brackets,

          %% If `version` is given, the option `--version` is automatically
          %% added to the main command.
          version => string(),

          %% If `add_help_option` is set to `true`, `-h|--help` is added to
          %% the command and all subcommands.
          add_help_option => boolean(), % default is 'true'

          %% If `add_completion_option` is set to `true`, `--completion`
          %% is added to the command.
          add_completion_option => boolean, % default is 'true'

          %% If `print_usage_on_error` is set to 'true', a message will
          %% be printed to stderr if parsing of the command line failed,
          %% and the command will exit with code 1.
          print_usage_on_error => boolean(), % default is 'true'

          %% A user-defined term.  Useful to pass data to callbacks.
          user => term()
         }.

%% A document can be used to get more control over how a command's help
%% text is formatted.  It can be used to print paragraphs, lists etc.
%% A nested document is indented one more level.
-type doc() :: {doc, [p() | ul() | dl() | pre() | doc()]}.

%% A paragraph of text.
-type p() :: {p, string()}.

%% An unordered list of strings.
-type ul() :: {ul, [string()]}.

%% A description list.
-type dl() :: {dl, [{Term :: string(), Text :: string()}]}.

%% A pre-formatted string.
-type pre() :: {pre, string()}.


-spec default_help_opt() -> opt().
%% Returns the option spec for `-h|--help`.
default_help_opt() ->
    #{name => help, short => $h, long => "help", type => flag,
      expose_value => false, cb => fun opt_help/3,
      help => "Show this help and exit"}.

-spec opt_help(parse_env(), result_opts(), cmd_stack()) -> no_return().
opt_help(Env, _Opts, CmdStack) ->
    print_help(standard_io, Env, CmdStack),
    throw({done, ok}).

-spec default_version_opt() -> opt().
%% Returns the option spec for `--version`.
default_version_opt() ->
    #{name => version, long => "version", type => flag,
      expose_value => false, cb => fun opt_version/3,
      help => "Print current version and exit"}.

-spec opt_version(parse_env(), result_opts(), cmd_stack()) -> no_return().
opt_version({#{name := Cmd}, #{version := Vsn}}, _, _) ->
    io:format("~ts ~ts\n", [Cmd, Vsn]),
    throw({done, ok}).

-spec default_completion_opt() -> opt().
%% Returns the option spec for `--completion`.
default_completion_opt() ->
    #{name => completion, long => "completion",
      args => [#{name => shell, type => {enum, [bash, zsh]}, nargs => '?'}],
      expose_value => false,
      help => "Print sourceable bash/zsh completion script. "
              "If no parameter is given, a guess will be made based on $SHELL.",
      cb => fun opt_completion/3}.

-spec opt_completion(parse_env(), result_opts(), cmd_stack()) -> no_return().
opt_completion({#{cmd := Cmd}, _}, ResultOpts, _) ->
    Shell =
        case maps:find(completion, ResultOpts) of
            {ok, #{shell := Shell0}} when Shell0 /= undefined ->
                Shell0;
            _ ->
                try_detect_shell()
        end,
    print_completion_script(Cmd, Shell),
    throw({done, ok}).

%% @parse/2
-spec parse(CmdLine :: [string()],
            CmdSpec :: cmd()) ->
    {done, term()}
  | {ok, parse_result()}
  | {error, Error :: term()}
  | CbRes :: term()
  .
%% Equivalent to `parse(CmdLine, CmdSpec, #{})`.
parse(CmdName, Cmd) ->
    parse(CmdName, Cmd, #{}).


%% @parse/3
-spec parse(CmdLine :: [string()],
            CmdSpec :: cmd(),
            Options :: parse_opts()) ->
    {done, term()}
  | {ok, parse_result()}
  | {error, Error :: term()}
  | CbRes :: term()
  .
%% Parse a command line of strings according to the `CmdSpec`.
%%
%% If there is an error in `CmdSpec`, an `error` is raised, on the
%% form `{error, term()}`.
%%
%% If parsing fails, a message is printed to the user, and
%% `{error, term()}` is returned.  The message can be suppressed with
%% the parse option `print_usage_on_error => false`.
%%
%% If the selected command (main or subcommand) has a callback defined,
%% the return value from the callback is returned, unless it returns
%% `{error, ErrMsg :: iodata(), Reason :: term()}`, in which case
%% parsing fails and `ErrMsg` is printed to the user (see above), and
%% `parse()` returns `{error, Reason}`.
%%
%% If any option's callback throws `{done, term()}`, this is returned.
%%
%% Otherwise, parsing succeeds and no callback was invoked, the
%% `parse` function returns `{ok, parse_result()}`.
parse(CmdLine0, Cmd0, ParseOpts0) ->
    Cmd1 =
        case maps:is_key(version, ParseOpts0) of
            true ->
                add_opt(default_version_opt(), Cmd0);
            false ->
                Cmd0
        end,
    Cmd2 =
        case maps:get(add_completion_option, ParseOpts0, true) of
            true ->
                add_opt(default_completion_opt(), Cmd1);
            false ->
                Cmd1
        end,
    try
        Cmd3 = prepare_main_cmd(Cmd2),
        {IsCompletion, CmdLine, ParseOpts} =
            case os:getenv("COMP_LAST_WORD") of
                false ->
                    {false, CmdLine0, ParseOpts0};
                "" ->
                    CmdLine1 = tl(CmdLine0),
                    {true, CmdLine1, ParseOpts0#{'_comp_word' => undefined}};
                CompWord ->
                    CmdLine1 = lists:reverse(tl(lists:reverse(tl(CmdLine0)))),
                    {true, CmdLine1, ParseOpts0#{'_comp_word' => CompWord}}
            end,
        case parse_cmd(CmdLine, Cmd3, ParseOpts, []) of
            {ok, ParseRes} when IsCompletion ->
                print_suggestions(ParseRes),
                halt(0);
            _ when IsCompletion ->
                halt(1);
            {error, _} = Error ->
                case maps:get(print_usage_on_error, ParseOpts, true) of
                    true ->
                        io:put_chars(
                          standard_error,
                          ["Error: ", fmt_error(Error),
                           ?nl, ?nl,
                           fmt_error_usage(Cmd3, [], ParseOpts)]),
                        halt(1);
                    false ->
                        ok
                end,
                case Error of
                    {error, {cb_error, _, Reason}} -> % unwrap cb err
                        {error, Reason};
                    _ ->
                        Error
                end;
            Res ->
                Res
        end
    catch
        throw:{done, _} = Done ->
            Done
    end.

parse_cmd(CmdLine, Cmd0, ParseOpts, CmdStack) ->
    Cmd1 =
        case maps:get(add_help_option, ParseOpts, true) of
            false ->
                Cmd0;
            true ->
                add_opt(default_help_opt(), Cmd0)
        end,
    Env = {Cmd1, ParseOpts},
    Cmd = flatten_cmd(Cmd1),
    CmdStr = maps:get(cmd, Cmd),
    case
        parse_opts(CmdLine, maps:get(opts, Cmd), CmdStr, Env, #{}, CmdStack)
    of
        {ok, RestCmdLine, ResultOpts0} ->
            case
                set_defaults(maps:get(opts, Cmd, []), ResultOpts0,
                             CmdStr, Env, CmdStack)
            of
                {ok, ResultOpts} ->
                    case maps:get(args, Cmd, undefined) of
                        undefined when RestCmdLine =/= [] ->
                            case maps:get('_cmdmap', Cmd, undefined) of
                                undefined ->
                                    {error,
                                     {unexpected_args, CmdStr, RestCmdLine}};
                                CmdMap ->
                                    parse_sub_cmd(RestCmdLine, CmdMap, CmdStr,
                                                  Env,
                                                  [{Cmd, ResultOpts} |
                                                   CmdStack])
                            end;
                        undefined ->
                            handle_parsed_cmd(Cmd, Env, ResultOpts, #{},
                                              CmdStack);
                        Args ->
                            case
                                parse_args(Args, RestCmdLine, false,
                                           {cmd, CmdStr}, Env)
                            of
                                {ok, [], ResultArgs0} ->
                                    {ok, ResultArgs} =
                                        set_defaults(maps:get(args, Cmd, []),
                                                     ResultArgs0, CmdStr, Env,
                                                     CmdStack),
                                    handle_parsed_cmd(Cmd, Env, ResultOpts,
                                                      ResultArgs, CmdStack);
                                {ok, RestCmdLine1, _} ->
                                    {error,
                                     {unexpected_args, CmdStr, RestCmdLine1}};
                                Error ->
                                    Error
                            end
                    end;
                Error ->
                    Error
            end;
        Error ->
            Error
    end.

handle_parsed_cmd(_, {_, #{'_comp_word' := _}} = Env,
                  ResultOpts, ResultArgs, CmdStack) ->
    {ok, {Env, CmdStack, ResultOpts, ResultArgs}};
handle_parsed_cmd(#{cmd := CmdStr, require_cmd := true}, _, _, _, _) ->
    {error, {expected_subcmd, CmdStr}};
handle_parsed_cmd(Cmd, Env, ResultOpts, ResultArgs, CmdStack) ->
    case maps:find(cb, Cmd) of
        {ok, Cb} ->
            CbRes =
                case erlang:fun_info(Cb, arity) of
                    {arity, 1} ->
                        Cb({Env, CmdStack, ResultOpts, ResultArgs});
                    _ ->
                        A = [Env, CmdStack] ++
                            [get_val(Opt, ResultOpts) ||
                                Opt <- maps:get(opts, Cmd, []),
                                maps:get(expose_value, Opt, true)] ++
                            [get_val(Arg, ResultArgs) ||
                                Arg <- maps:get(args, Cmd, [])],
                        apply(Cb, A)
                end,
            case CbRes of
                {error, ErrMsg, Reason} ->
                    {error, {cb_error, ErrMsg, Reason}};
                _ ->
                    CbRes
            end;
        _ ->
            {ok, {Env, CmdStack, ResultOpts, ResultArgs}}
    end.

set_defaults(Items, ResultMap, CmdStr, Env, CmdStack) ->
    case is_completion(Env) of
        true ->
            {ok, ResultMap};
        false ->
            set_defaults0(Items, ResultMap, CmdStr, Env, CmdStack)
    end.

set_defaults0([#{name := Name, default := Default} = H | T], ResultMap0,
              CmdStr, Env, CmdStack) ->
    case maps:is_key(Name, ResultMap0) of
        true ->
            set_defaults0(T, ResultMap0, CmdStr, Env, CmdStack);
        false ->
            ResultMap1 = ResultMap0#{Name => Default},
            ResultMap2 =
                case H of
                    #{cb := Cb} ->
                        Cb(Env, ResultMap1, CmdStack);
                    _ ->
                        ResultMap1
                end,
            set_defaults0(T, ResultMap2, CmdStr, Env, CmdStack)
    end;
set_defaults0([#{name := Name, required := true} = H | T], ResultMap,
              CmdStr, Env, CmdStack) ->
    case maps:is_key(Name, ResultMap) of
        true ->
            set_defaults0(T, ResultMap, CmdStr, Env, CmdStack);
        false ->
            OptStr =
                case {maps:get(short, H, undef), maps:get(long, H, undef)} of
                    {Ch, undef} ->
                        [$-, Ch];
                    {undef, Long} ->
                        [$-, $- | Long];
                    {Ch, Long} ->
                        [$-, Ch, $\s, $|, $\s, $-, $- | Long]
                end,
            {error, {expected_opt, CmdStr, OptStr}}
    end;
set_defaults0([_ | T], ResultMap, CmdStr, Env, CmdStack) ->
    set_defaults0(T, ResultMap, CmdStr, Env, CmdStack);
set_defaults0([], ResultMap, _CmdStr, _Env, _CmdStack) ->
    {ok, ResultMap}.

get_val(#{name := Name} = Item, ResultItems) ->
    maps:get(Name, ResultItems,
             maps:get(default, Item, undefined)).

parse_sub_cmd([SubCmdStr | T], CmdMap, CmdStr, {_, ParseOpts}, CmdStack) ->
    case maps:find(SubCmdStr, CmdMap) of
        {ok, SubCmdSpec} ->
            parse_cmd(T, SubCmdSpec, ParseOpts, CmdStack);
        error ->
            {error, {unknown_param, CmdStr, SubCmdStr}}
    end.

add_opt(Opt, Cmd) ->
    Opts = maps:get(opts, Cmd, []),
    Cmd#{opts => add_opt0(Opt, Opts)}.

add_opt0(Opt, [{group, Opts} | T]) ->
    [{group, add_opt0(Opt, Opts)} | T];
add_opt0(Opt, Opts) ->
    [Opt | Opts].

flatten_cmd(Cmd) ->
    Opts = flatten_opts(maps:get(opts, Cmd, [])),
    Cmd#{opts => Opts}.

flatten_opts([{group, _, Opts} | T]) ->
    flatten_opts(Opts ++ T);
%flatten_opts([{choice, OptsL} | T]) ->
%    lists:foldl(fun(Opts, Acc) ->
%                        Acc ++ flatten_opts(Opts)
%                end, [], OptsL) ++
%        flatten_opts(T);
flatten_opts([H | T]) ->
    [H | flatten_opts(T)];
flatten_opts([]) ->
    [].

%% validates the given spec, and fills in defaults etc.
prepare_main_cmd(Cmd0) ->
    %% ensure
    Cmd1 =
        case Cmd0 of
            #{cmd := _} ->
                Cmd0;
            _ ->
                Cmd0#{cmd => filename:basename(hd(init:get_plain_arguments()))}
        end,
    prepare_cmd(Cmd1).

prepare_cmd(Cmd0) ->
    Cmd =
        case Cmd0 of
            #{name := _} ->
                Cmd0;
            #{cmd := CmdStr} ->
                Cmd0#{name => str_to_name(CmdStr)}
        end,
    case Cmd of
        #{args := _, cmds := _} ->
            error({invalid_cmd, maps:get(name, Cmd), args_and_cmds});
        _ ->
            ok
    end,
    Opts = prepare_opts(maps:get(opts, Cmd, [])),
    CmdMap = prepare_cmds(maps:get(cmds, Cmd, []), #{}),
    Cmd1 = Cmd#{opts => Opts, '_cmdmap' => CmdMap},
    case maps:get(args, Cmd, undefined) of
        undefined ->
            Cmd1;
        Args ->
            Args1 = prepare_args(Args),
            Cmd1#{args => Args1}
    end.

prepare_opts([{group, Header, Opts} | T]) ->
    [{group, Header, prepare_opts(Opts)} | prepare_opts(T)];
%prepare_opts([{choice, OptsL} | T]) ->
%    [{choice, [prepare_opts(Opts) || Opts <- OptsL]} | prepare_opts(T)];
prepare_opts([Opt0 | T]) ->
    case {maps:is_key(short, Opt0), maps:is_key(long, Opt0)} of
        {false, false} ->
            error({invalid_opt, maps:get(name, Opt0, Opt0),
                   no_short_no_long});
        _ ->
            ok
    end,
    Opt1 =
        case Opt0 of
            #{name := _} ->
                Opt0;
            #{long := Long} ->
                Opt0#{name => str_to_name(Long)};
            #{short := Char} ->
                Opt0#{name => ?l2a([Char])}
        end,
    Opt2 =
        case Opt1 of
            #{name := Name, type := _, args := _} ->
                error({invalid_opt, Name, type_and_args});
            #{type := count} ->
                Opt1#{multiple => true};
            #{name := Name, type := Type} ->
                validate_opt_type(Name, Type),
                Opt1;
            #{name := Name, args := Args} ->
                lists:foreach(fun(#{name := AName, nargs := NArgs})
                                    when not (is_integer(NArgs)
                                              orelse NArgs == '?') ->
                                      error({invalid_opt, Name,
                                             {bad_nargs, AName}});
                                 (_) ->
                                      ok
                              end, Args),
                Opt1;
            #{default := Default} ->
                if is_integer(Default) ->
                        Opt1#{type => int};
                   is_float(Default) ->
                        Opt1#{type => float};
                   Default == true ->
                        Opt1#{type => boolean};
                   Default == false ->
                        Opt1#{type => boolean};
                   true ->
                        Opt1#{type => string}
                end;
            _ ->
                Opt1#{type => string}
        end,
    Opt3 = prepare_opt_help(Opt2),
    Opt4 = prepare_opt_default(Opt3),
    [Opt4 | prepare_opts(T)];
prepare_opts([]) ->
    [].

validate_opt_type(Name, Type) ->
    case Type of
        flag ->
            ok;
        boolean ->
            ok;
        count ->
            ok;
        _ ->
            ArgType =
                case Type of
                    #{type := ArgType0} ->
                        ArgType0;
                    _ ->
                        Type
                end,
            try
                validate_arg_type(Name, ArgType)
            catch error:{invalid_arg, Name, Reason} ->
                    error({invalid_opt, Name, Reason})
            end
    end.

validate_arg_type(Name, Type) ->
    try
        case Type of
            dir ->
                ok;
            file ->
                ok;
            string ->
                ok;
            {string, Regexps} ->
                true = lists:all(
                         fun(Re) -> case re:compile(Re) of
                                        {ok, _} -> true
                                    end
                         end, Regexps);
            {enum, Enums} ->
                lists:all(fun(E) -> is_atom(E) end, Enums);
            int ->
                ok;
            {int, Ranges} when is_list(Ranges) ->
                ok;
            float ->
                ok;
            {float, Ranges} when is_list(Ranges) ->
                ok;
            {custom, Fun} when is_function(Fun) ->
                ok
        end
    catch
        _:_ ->
            error({invalid_arg, Name, {bad_type, Type}})
    end.

prepare_opt_help(Opt0) ->
    Opt1 = p_opt_help_enum(Opt0),
    Opt2 = p_opt_help_default(Opt1),
    Opt2.

p_opt_help_enum(#{enum_in_help := false} = Opt) ->
    Opt;
p_opt_help_enum(#{type := {enum, Enums}} = Opt) ->
    HelpStr =
        case maps:get(help, Opt, []) of
            [] ->
                "";
            HelpStr0 ->
                case binary:last(iolist_to_binary(HelpStr0)) of
                    $. ->
                        [HelpStr0, " "];
                    _ ->
                        [HelpStr0, ". "]
                end
        end,
    EnumStr =
        ["One of ", lists:join(", ", [?a2l(E) || E <- Enums]), "."],
    Opt#{help => [HelpStr, EnumStr]};
p_opt_help_enum(Opt) ->
    Opt.


p_opt_help_default(#{default_in_help := false} = Opt) ->
    Opt;
p_opt_help_default(#{help := HelpStr, type := boolean, long := LOpt} = Opt) ->
    DefStr =
        case maps:get(default, Opt, false) of
            true -> [" (default: ", LOpt, ")"];
            false -> [" (default: no-", LOpt, ")"]
        end,
    Opt#{help => [HelpStr, DefStr]};
p_opt_help_default(#{type := boolean, long := LOpt} = Opt) ->
    DefStr =
        case maps:get(default, Opt, false) of
            true -> ["Default: ", LOpt];
            false -> ["Default: no-", LOpt]
        end,
    Opt#{help => DefStr};
p_opt_help_default(#{type := boolean} = Opt) ->
    Opt;
p_opt_help_default(#{default := Default, help := HelpStr} = Opt) ->
    DefStr = io_lib:format(" (default: ~p)", [Default]),
    Opt#{help => [HelpStr, DefStr]};
p_opt_help_default(#{default := Default} = Opt) ->
    DefStr = io_lib:format("Default: ~p", [Default]),
    Opt#{help => DefStr};
p_opt_help_default(Opt) ->
    Opt.


prepare_opt_default(#{default := _} = Opt) ->
    Opt;
prepare_opt_default(Opt) ->
    case Opt of
        #{type := count} ->
            Opt#{default => 0};
        #{multiple := true} ->
            Opt#{default => []};
        #{type := flag} ->
            Opt#{default => false};
        #{type := boolean} ->
            Opt#{default => false};
        _ ->
            Opt
    end.

prepare_cmds([{group, _, Cmds} | T], Acc) ->
    prepare_cmds(Cmds ++ T, Acc);
prepare_cmds([#{cmd := CmdStr} = Cmd | T], Acc) ->
    prepare_cmds(T, Acc#{CmdStr => prepare_cmd(Cmd)});
prepare_cmds([Cmd | _], _) ->
    error({invalid_cmd, Cmd, {missing, cmd}});
prepare_cmds([], Acc) ->
    Acc.

prepare_args(Args0) ->
    Args1 = [prepare_arg(Arg) || Arg <- Args0],
    validate_nargs(Args1),
    Args1.

prepare_arg(#{name := Name} = Arg0) ->
    Arg1 =
        case maps:find(type, Arg0) of
            {ok, Type} ->
                validate_arg_type(Name, Type),
                Arg0;
            _ ->
                Arg0#{type => string}
        end,
    Arg2 =
        case maps:is_key(nargs, Arg1) of
            true ->
                Arg1;
            false ->
                Arg1#{nargs => 1}
        end,
    Arg2;
prepare_arg(Arg) ->
    error({invalid_arg, Arg, {missing, name}}).


validate_nargs(Args) ->
    validate_nargs(Args, false).

validate_nargs([#{name := Name, nargs := NArg}, _ | _], _)
  when NArg =:= '*' orelse NArg =:= '+' ->
    error({invalid_arg, Name, multi_narg_not_at_end});
validate_nargs([#{name := Name, nargs := NArg} | _], true)
  when NArg =/= '?' ->
    error({invalid_arg, Name, non_optional_follows_optional});
validate_nargs([#{nargs := '?'} | T], _) ->
    validate_nargs(T, true);
validate_nargs([_ | T], OptionalFound) ->
    validate_nargs(T, OptionalFound);
validate_nargs([], _) ->
    ok.

parse_opts(["--" | T], _Opts, _CmdStr, _Env, OptsAcc, _CmdStack) ->
    {ok, T, OptsAcc};
parse_opts(["--no-" ++ LOpt | T], Opts, CmdStr, Env, OptsAcc0, CmdStack) ->
    %% first check if this is a boolean option
    case match_opt(LOpt, long, Opts, CmdStr, OptsAcc0) of
        {ok, #{name := Name, type := boolean}} ->
            OptsAcc1 = OptsAcc0#{Name => false},
            parse_opts(T, Opts, CmdStr, Env, OptsAcc1, CmdStack);
        _ ->
            %% else fall back to normal parsing of long opts
            parse_lopt("no-" ++ LOpt, T, Opts, CmdStr, Env, OptsAcc0, CmdStack)
    end;
parse_opts(["--" ++ LOpt | T], Opts, CmdStr, Env, OptsAcc, CmdStack) ->
    parse_lopt(LOpt, T, Opts, CmdStr, Env, OptsAcc, CmdStack);
parse_opts(["-" ++ SOptL | T], Opts, CmdStr, Env, OptsAcc, CmdStack)
  when SOptL /= [] ->
    parse_sopts(SOptL, T, Opts, CmdStr, Env, OptsAcc, CmdStack);
parse_opts(RestCmdLine, _Opts, _CmdStr, _Env, OptsAcc, _CmdStack) ->
    {ok, RestCmdLine, OptsAcc}.

parse_lopt(LOpt, Args, Opts, CmdStr, Env, OptsAcc, CmdStack) ->
    case match_opt(LOpt, long, Opts, CmdStr, OptsAcc) of
        {ok, Opt} ->
            handle_opt_and_continue(Opt, long, Args, Opts, CmdStr,
                                    Env, OptsAcc, CmdStack);
        Else ->
            Else
    end.

parse_sopts([SOpt], Args, Opts, CmdStr, Env, OptsAcc, CmdStack) ->
    %% last short option, may take an argument
    case match_opt(SOpt, short, Opts, CmdStr, OptsAcc) of
        {ok, Opt} ->
            handle_opt_and_continue(Opt, short, Args, Opts, CmdStr,
                                    Env, OptsAcc, CmdStack);
        Else ->
            Else
    end;
parse_sopts([SOpt | T], Args, Opts, CmdStr, Env, OptsAcc0, CmdStack) ->
    %% clustered short option that must not take an argument
    case match_opt(SOpt, short, Opts, CmdStr, OptsAcc0) of
        {ok, #{type := Type} = Opt}
          when Type =:= count;
               Type =:= flag;
               Type =:= boolean ->
            {ok, [], OptsAcc1} =
                handle_opt(Opt, short, [], OptsAcc0, Env, CmdStack),
            parse_sopts(T, Args, Opts, CmdStr, Env, OptsAcc1, CmdStack);
        {ok, _} ->
            {error, {opt_needs_argument, CmdStr, [$-, SOpt]}};
        Error ->
            Error
    end.

match_opt(GivenOpt, Style, [Opt | T], CmdStr, OptsAcc) ->
    case Opt of
        #{Style := GivenOpt} ->
            case Opt of
                #{multiple := true} ->
                    {ok, Opt};
                #{name := Name} ->
                    case maps:is_key(Name, OptsAcc) of
                        false ->
                            {ok, Opt};
                        true ->
                            OptStr = opt_str(Style, GivenOpt),
                            {error, {opt_already_given, CmdStr, OptStr}}
                    end
            end;
        _ ->
            match_opt(GivenOpt, Style, T, CmdStr, OptsAcc)
    end;
match_opt(GivenOpt, Style, [], CmdStr, _) ->
    OptStr = opt_str(Style, GivenOpt),
    {error, {unknown_opt, CmdStr, OptStr}}.

opt_str(short, GivenOpt) ->
    [$-, GivenOpt];
opt_str(long, GivenOpt) ->
    [$-, $- | GivenOpt].


handle_opt_and_continue(Opt, Style, Args0, Opts, CmdStr, Env,
                        OptsAcc0, CmdStack) ->
    case handle_opt(Opt, Style, Args0, OptsAcc0, Env, CmdStack) of
        {ok, Args1, OptsAcc1} ->
            parse_opts(Args1, Opts, CmdStr, Env, OptsAcc1, CmdStack);
        Error ->
            Error
    end.

handle_opt(#{name := Name} = Opt, Style, CmdLine0, OptsAcc, Env, CmdStack) ->
    Multiple = maps:get(multiple, Opt, false),
    case Opt of
        #{type := count} ->
            Cnt0 = maps:get(Name, OptsAcc, 0),
            ret_opt(Opt, CmdLine0, OptsAcc, Cnt0 + 1, Env, CmdStack);
        #{type := flag} ->
            ret_opt(Opt, CmdLine0, OptsAcc, true, Env, CmdStack);
        #{type := boolean} ->
            ret_opt(Opt, CmdLine0, OptsAcc, true, Env, CmdStack);
        #{type := Type} ->
            Arg =
                if is_map(Type) ->
                        Type#{name => Name};
                   true ->
                        #{name => Name, type => Type, nargs => 1}
                end,
            StopOnOpt = maps:get(nargs, Arg, 1) == '?',
            case
                parse_args([Arg], CmdLine0, StopOnOpt, {opt, Style, Opt}, Env)
            of
                {ok, CmdLine1, #{Name := ArgVal}} when not Multiple ->
                    ret_opt(Opt, CmdLine1, OptsAcc, ArgVal, Env, CmdStack);
                {ok, CmdLine1, #{Name := ArgVal}} ->
                    ArgVals = maps:get(Name, OptsAcc, []),
                    ret_opt(Opt, CmdLine1, OptsAcc,
                            ArgVals ++ [ArgVal], Env, CmdStack);
                Else ->
                    Else
            end;
        #{args := ArgSpecs} ->
            case parse_args(ArgSpecs, CmdLine0, true, {opt, Style, Opt}, Env) of
                {ok, CmdLine1, ResultArgs} when not Multiple ->
                    ret_opt(Opt, CmdLine1, OptsAcc, ResultArgs, Env, CmdStack);
                {ok, CmdLine1, ResultArgs} ->
                    ResultArgsL = maps:get(Name, OptsAcc, []),
                    ret_opt(Opt, CmdLine1, OptsAcc,
                            ResultArgsL ++ [ResultArgs], Env, CmdStack);
                Else ->
                    Else
            end
    end.

ret_opt(#{name := Name} = Opt, CmdLine, OptsAcc0, NewVal, Env, CmdStack) ->
    IsCompletion = is_completion(Env),
    OptsAcc1 = OptsAcc0#{Name => NewVal},
    OptsAcc2 =
        case Opt of
            #{cb := Cb} when not IsCompletion ->
                case erlang:fun_info(Cb, arity) of
                    {arity, 2} ->
                        Cb(Env, OptsAcc1);
                    {arity, 3} ->
                        Cb(Env, OptsAcc1, CmdStack)
                end;
            _ ->
                OptsAcc1
        end,
    {ok, CmdLine, OptsAcc2}.


parse_args(ArgSpecs, CmdLine, StopOnOpt, From, Env) ->
    parse_args(ArgSpecs, CmdLine, StopOnOpt, From, Env, #{}).

parse_args([#{name := Name} = H | T], CmdLine0, StopOnOpt, From, Env, Acc) ->
    Type = maps:get(type, H, string),
    NArgs = maps:get(nargs, H, 1),
    Compword = get_comp_word(Env),
    if (Type == dir orelse Type == file)
       andalso CmdLine0  == []
       andalso (Compword == undefined orelse hd(Compword) /= $-) ->
            print_special_suggestion(Type),
            halt(0);
       is_integer(NArgs) orelse
       ((NArgs == '+' orelse NArgs == '*') andalso CmdLine0 =/= []) ->
            case consume_args(CmdLine0, Type, NArgs) of
                {ok, CmdLine1, [ArgVal]} when NArgs == 1 ->
                    parse_args(T, CmdLine1, StopOnOpt, From, Env,
                               Acc#{Name => ArgVal});
                {ok, CmdLine1, ArgVals} ->
                    parse_args(T, CmdLine1, StopOnOpt, From, Env,
                               Acc#{Name => ArgVals});
                {error, {Tag, Details}} ->
                    IsOpt = case From of
                                {opt, _, _} -> true;
                                _ -> false
                            end,
                    case is_completion(Env) of
                        true when Tag == missing_args andalso not IsOpt ->
                            parse_args([], CmdLine0, StopOnOpt, From, Env, Acc);
                        _ ->
                            %% Add From to the error message
                            case From of
                                {cmd, CmdStr} ->
                                    %% for commands, we print the arg
                                    %% in the error
                                    MV = arg_metavar_env(H, Env),
                                    {error, {Tag, {arg, MV, CmdStr}, Details}};
                                _ ->
                                    {error, {Tag, From, Details}}
                            end
                    end
            end;
       (NArgs == '?' orelse NArgs == '*') andalso CmdLine0 =:= [] ->
            Val = maps:get(default, H, undefined),
            parse_args(T, CmdLine0, StopOnOpt, From, Env, Acc#{Name => Val});
       NArgs == '?' ->
            [Str | CmdLine1] = CmdLine0,
            case match_arg(Str, Type, StopOnOpt) of
                {ok, ArgVal} ->
                    parse_args(T, CmdLine1, StopOnOpt, From, Env,
                               Acc#{Name => ArgVal});
                nomatch ->
                    Val = maps:get(default, H, undefined),
                    parse_args(T, CmdLine0, StopOnOpt, From, Env,
                               Acc#{Name => Val});
                Error ->
                    Error
            end;
       NArgs == '+' andalso CmdLine0 == [] ->
            case is_completion(Env) of
                false ->
                    {error, {expected_arg, From}};
                true ->
                    parse_args(T, CmdLine0, StopOnOpt, From, Env, Acc)
            end
    end;
parse_args([], CmdLine, _, _, _, Acc) ->
    {ok, CmdLine, Acc}.

consume_args(Args, Type, NArgs) ->
    N = if is_integer(NArgs) ->
                NArgs;
           true ->
                -1
        end,
    do_consume_args(Args, Type, N, []).

do_consume_args([], _, NArgs, Acc) when NArgs =< 0 ->
    {ok, [], lists:reverse(Acc)};
do_consume_args(CmdLine, _, 0, Acc) ->
    {ok, CmdLine, lists:reverse(Acc)};
do_consume_args([H | T], Type, N, Acc) ->
    case match_arg(H, Type, false) of
        {ok, ArgVal} ->
            do_consume_args(T, Type, N-1, [ArgVal | Acc]);
        Error ->
            Error
    end;
do_consume_args(_, _, NArgs, _) ->
    {error, {missing_args, NArgs}}.

%% Match a given argument string to the expected type.
match_arg([$- | _], _, _StopOnOpt = true) ->
    %% this means that we're parsing an *optional* argument
    %% to an option.  e.g., "--foo --bar" - is "--bar" an argument
    %% to "--foo" or a separate option.  we treat it as a separate option.
    nomatch;
match_arg(Arg, string, _) ->
    {ok, Arg};
match_arg(Arg, Type, _) ->
    try
        case Type of
            dir ->
                {ok, Arg};
            file ->
                {ok, Arg};
            string ->
                {ok, Arg};
            {string, Regexps} ->
                true = lists:all(
                         fun(Re) -> case re:run(Arg, Re) of
                                        {match, _} -> true;
                                        _ -> false
                                    end
                         end, Regexps),
                {ok, Arg};
            {enum, Enums} ->
                ArgAtom = list_to_existing_atom(Arg),
                true = lists:member(ArgAtom, Enums),
                {ok, ArgAtom};
            int ->
                Val = list_to_integer(Arg),
                {ok, Val};
            {int, Ranges} ->
                Val = list_to_integer(Arg),
                chk_ranges(Ranges, Val),
                {ok, Val};
            float ->
                Val = to_float(Arg),
                {ok, Val};
            {float, Ranges} ->
                Val = to_float(Arg),
                chk_ranges(Ranges, Val),
                {ok, Val};
            {custom, Fun} ->
                case Fun(Arg) of
                    {ok, _Term} = Ok ->
                        Ok;
                    _Error ->
                        throw(error)
                end
        end
    catch
        _:_ ->
            {error, {bad_arg, {Arg, Type}}}
    end.

to_float(Str) ->
    try list_to_integer(Str) of
        Int ->
            Int / 1.0
    catch
        _:_ ->
            list_to_float(Str)
    end.


chk_ranges([Val | _], Val) ->
    ok;
chk_ranges([{Min, Max} | _], Val)
  when (Min == unbounded orelse Min =< Val) andalso
       (Max == unbounded orelse Val =< Max) ->
    ok;
chk_ranges([_ | T], Val) ->
    chk_ranges(T, Val).


%%% Help formatting

%% @print_help/2
-spec print_help(Env :: parse_env(), CmdStack :: cmd_stack()) -> ok.
%% Equivalent to `print_help(standard_io, Env, CmdStack)`.
print_help(Env, CmdStack) ->
    print_help(standard_io, Env, CmdStack).

%% @print_help/3
-spec print_help(io:device(), parse_env(), cmd_stack()) -> ok.
%% Prints the help text to the given io device.
print_help(Fd, Env, CmdStack) ->
    Width =
        case io:columns(Fd) of
            {ok, Cols} ->
                %% use the interval [50, 120]
                max(min(Cols, 120), 50);
            _ ->
                79
        end,
    Col = ceil(Width / 2.8), % carefully selected to get 29 when Width is 79
    io:put_chars(Fd, fmt_help(Env, CmdStack, {Width, Col})).

%% @fmt_help/2
-spec fmt_help(Env :: parse_env(), CmdStack :: cmd_stack()) ->
          unicode:chardata().
%% Equivalent to `fmt_help(Env, CmdStack, {79, 29})`.
fmt_help(Env, CmdStack) ->
    fmt_help(Env, CmdStack, {79, 29}).

%% @fmt_help/3
-spec fmt_help(parse_env(),
               cmd_stack(),
               Sz :: {Width :: integer(), Col :: integer()}) ->
          unicode:chardata().
%% Formats the help text with the given `Width` and help text starting
%% at column `Col`.
fmt_help({Cmd, ParseOpts}, CmdStack, Sz) ->
    MStyle = maps:get(metavar_style, ParseOpts, caps),
    Sections =
        [fmt_usage(Cmd, CmdStack, MStyle),
         fmt_cmd_help(Cmd, Sz),
         fmt_opts(Cmd, MStyle, Sz),
         fmt_cmds(Cmd, Sz)],
    lists:join(?nl, [S || S <- Sections, S /= ""]).

fmt_usage(#{cmd := CmdStr0} = Cmd, CmdStack, MStyle) ->
    CmdStr =
        lists:join($\s,
                   lists:foldl(fun({#{cmd := CmdStr1}, _}, Acc) ->
                                       [CmdStr1 | Acc]
                               end, [CmdStr0], CmdStack)),
    OptionsStr =
        case maps:get(opts, Cmd, []) of
            [] ->
                "";
            _ ->
                [$\s, $[, fmt_metavar("options", MStyle), $]]
        end,
    case Cmd of
        #{args := Args} ->
            ArgsStr = fmt_args_metavars(Args, MStyle),
            ["Usage: ", CmdStr, OptionsStr, " ", ArgsStr, ?nl];
        #{cmds := _} ->
            SubCmdStr = fmt_metavar("command", MStyle),
            SubCmdArgs = fmt_metavar("args", MStyle),
            ["Usage: ", CmdStr, OptionsStr, " ",
             SubCmdStr, " [", SubCmdArgs, "]", ?nl];
        _ ->
            ["Usage: ", CmdStr, OptionsStr, ?nl]
    end.

fmt_error_usage(#{cmd := CmdStr} = Cmd, CmdStack, ParseOpts) ->
    MStyle = maps:get(metavar_style, ParseOpts, caps),
    [fmt_usage(Cmd, CmdStack, MStyle),
     case maps:get(default_help_opt, ParseOpts, true) of
         true ->
             ["Try '", CmdStr, " --help' for more information."];
         false ->
             []
     end,
     ?nl].

fmt_cmd_help(#{help := {doc, Doc}}, {W, _C}) ->
    fmt_doc(Doc, W, 2);
fmt_cmd_help(#{help := Help}, {W, _C}) ->
    Pars = string:split(Help, "\n\n", all),
    fmt_doc([{p, Text} || Text <- Pars], W, 2);
fmt_cmd_help(_, _) ->
    "".

fmt_doc([{p, Text} | T], W, C) ->
    [prettypr:format(prettypr:nest(C, prettypr:text_par(Text)), W, W), ?nl,
     break(T) |
     fmt_doc(T, W, C)];
fmt_doc([{ul, Text, Items} | T], W, C) ->
    TC = C + 4,
    [prettypr:format(prettypr:nest(C, prettypr:text_par(Text)), W, W), ?nl,
     [fmt_list_item([sp(C+2), "o"], ItemText, W-TC, TC) || ItemText <- Items],
     break(T) |
     fmt_doc(T, W, C)];
fmt_doc([{dl, Text, Items} | T], W, C) ->
     MaxDefL = 8 + lists:max([length(Def) || {Def, _} <- Items]),
     TC = if MaxDefL >= W -> 8;
            true -> MaxDefL
         end,
    [prettypr:format(prettypr:nest(2, prettypr:text_par(Text)), W, W), ?nl,
     [fmt_list_item(["    ", Def], ItemText, W-TC, TC) ||
         {Def, ItemText} <- Items],
     break(T) |
     fmt_doc(T, W, C)];
fmt_doc([{pre, Text} | T], W, C) ->
    Lines = split_lines(Text),
    [[[sp(C), Line, ?nl] || Line <- Lines],
     break(T) |
     fmt_doc(T, W, C)];
fmt_doc([{doc, Doc} | T], W, C) ->
    [fmt_doc(Doc, W, C+2),
     break(T) |
     fmt_doc(T, W, C)];
fmt_doc([], _, _) ->
    [].

sp(N) ->
    lists:duplicate(N, $\s).

break([]) -> [];
break(_) -> ?nl.

fmt_opts(#{opts := Opts}, MStyle, Sz) when Opts /= [] ->
    OptsSections = mk_sections(Opts, "Options"),
    lists:join(?nl, [fmt_opts_section(S, MStyle, Sz) || S <- OptsSections]);
fmt_opts(_, _, _) ->
    "".

fmt_opts_section({Header, Opts}, MStyle, Sz) ->
    [if Header /= [] -> [Header, $:];
        true -> ""
     end, ?nl,
     [fmt_opt(Opt, MStyle, Sz) || Opt <- flatten_opts(Opts),
                                  maps:get(help, Opt, "") /= hidden]].

fmt_opt(Opt, MStyle, Sz) ->
    OptStr =
        case
            {maps:get(short, Opt, undef),
             maps:get(long, Opt, undef),
             maps:get(type, Opt, undef)} of
            {Ch, undef, _} ->
                [$-, Ch, $\s, $\s];
            {undef, Long, Type} ->
                "    --" ++ Long ++
                    if Type == boolean -> " / --no-" ++ Long;
                       true -> ""
                    end;
            {Ch, Long, Type} ->
                [$-, Ch, $,, $\s] ++ "--" ++ Long ++
                    if Type == boolean -> " / --no-" ++ Long;
                       true -> ""
                    end
        end,
    MetavarStr = case fmt_opt_metavar(Opt, MStyle) of
                     "" -> "";
                     M -> lists:flatten([$\s | M])
                 end,
    Pre = "  " ++ OptStr ++ MetavarStr,
    case Opt of
        #{help := HelpStr} ->
            {W, C} = Sz,
            fmt_list_item(Pre, HelpStr, W, C);
        _ ->
            [Pre, ?nl]
    end.

fmt_opt_metavar(Opt, MStyle) ->
    case Opt of
        #{type := Type} when Type =:= count; Type =:= flag; Type =:= boolean ->
            "";
        #{args := Args} ->
            fmt_args_metavars(Args, MStyle);
        #{name := Name, type := Arg0} when is_map(Arg0) ->
            Arg1 = case maps:is_key(name, Arg0) of
                       true -> Arg0;
                       false -> Arg0#{name => Name}
                   end,
            fmt_arg_metavar(Arg1, MStyle);
        #{metavar := MVar} ->
            MVar;
        #{name := Name} ->
            fmt_metavar(?a2l(Name), MStyle)
    end.

fmt_args_metavars(Args, MStyle) ->
    lists:join(" ", [fmt_arg_metavar(A, MStyle) || A <- Args]).

fmt_arg_metavar(A, MStyle) ->
    MVar = arg_metavar(A, MStyle),
    case maps:get(nargs, A, 1) of
        '?' -> [$[, MVar, $]];
        '*' -> [$[, MVar, $], "..."];
        '+' -> [MVar, "..."];
        N   -> lists:join(" ", lists:duplicate(N, MVar))
    end.

arg_metavar(#{metavar := MVar}, _MStyle) ->
    MVar;
arg_metavar(#{name := Name}, MStyle) ->
    fmt_metavar(?a2l(Name), MStyle).

arg_metavar_env(Arg, {_, ParseOpts}) ->
    MStyle = maps:get(metavar_style, ParseOpts, caps),
    arg_metavar(Arg, MStyle).

%% Format each command as:
%%   CMDSTR      HELP
%% Where HELP is indented to a column between 16, C
fmt_cmds(#{cmds := Cmds}, Sz) when Cmds /= [] ->
    CmdsSections = mk_sections(Cmds, "Commands"),
    MaxCmdLen = max_cmd_len(CmdsSections, 0),
    SuggestedC = 2 + MaxCmdLen + 2,
    {W, MaxC} = Sz,
    MinC = 16,
    C =
        if SuggestedC > MaxC ->
                MaxC;
           SuggestedC < MinC ->
                MinC;
           true ->
                SuggestedC
        end,
    lists:join(?nl, [fmt_cmds_section(S, W, C) || S <- CmdsSections]);
fmt_cmds(_, _) ->
    "".

max_cmd_len([{_, Cmds} | T], Max) ->
    max_cmd_len(T, max_cmd_len0(Cmds, Max));
max_cmd_len([], Max) ->
    Max.

max_cmd_len0([#{cmd := CmdStr} | T], Max) ->
    max_cmd_len0(T, max(length(CmdStr), Max));
max_cmd_len0([], Max) ->
    Max.

fmt_cmds_section({Header, Cmds}, W, C) ->
    [if Header /= [] -> [Header, $:];
        true -> ""
     end, ?nl,
     [fmt_cmd(Cmd, W, C) || Cmd <- Cmds]].

fmt_cmd(#{cmd := CmdStr} = Cmd, W, C) ->
    Pre = "  " ++ CmdStr,
    case Cmd of
        #{help := hidden} ->
            [];
        #{short_help := ShortHelpStr} ->
            fmt_list_item(Pre, ShortHelpStr, W, C);
        #{help := {doc, Doc}} ->
            HelpStr = binary_to_list(iolist_to_binary(fmt_doc(Doc, W, C))),
            ShortHelpStr = first_sentence(string:strip(HelpStr)),
            fmt_list_item(Pre, ShortHelpStr, W, C);
        #{help := HelpStr} ->
            ShortHelpStr = first_sentence(HelpStr),
            fmt_list_item(Pre, ShortHelpStr, W, C);
        _ ->
            [Pre, ?nl]
    end.

fmt_list_item(Pre, Str, W, C) ->
    [FirstL | RestLs] = Ls =
        split_lines(
          prettypr:format(prettypr:text_par(Str), W-C, W-C)),
    PreLen = string:length(Pre),
    if PreLen < C ->
            [string:pad(Pre, C), FirstL, ?nl |
             [[sp(C), L, ?nl] || L <- RestLs]];
       PreLen < W ->
            [Pre, ?nl,
             [[sp(C), L, ?nl] || L <- Ls]];
       true ->
            [prettypr:format(prettypr:text_par(Pre), W, W),
             ?nl,
             [[sp(C), L, ?nl] || L <- Ls]]
    end.

fmt_metavar(Word, caps) ->
    string:replace(string:uppercase(Word), "-", "_");
fmt_metavar(Word, brackets) ->
    [$<, Word, $>].

str_to_name(Str) ->
    ?l2a(lists:flatten(string:replace(Str, "-", "_"))).

mk_sections([], _) ->
    [];
mk_sections([{group, H, Items} | T], _) ->
    [{H, flatten_opts(Items)} |
     mk_sections(T, "")];
mk_sections(Items, Header) ->
    {ItemsInSection, Rest} =
        lists:splitwith(fun({group, _, _}) -> false;
                           (_) -> true
                        end, Items),
    [{Header, ItemsInSection} |
     mk_sections(Rest, "")].

first_sentence([$., C | _]) when C =:= $\s; C =:= $\n ->
    [];
first_sentence([$.]) ->
    [];
first_sentence([H | T]) ->
    [H | first_sentence(T)];
first_sentence([]) ->
    [].

split_lines(Str) ->
    re:split(Str, "\n", [{return, list}]).

fmt_error({error, Reason}) ->
    fmt_error(Reason);
fmt_error({cb_error, ErrMsg, _}) ->
    ErrMsg;
fmt_error({unexpected_args, CmdStr, [Word | _CmdLine]}) ->
    io_lib:format("unexpected argument \"~s\" to ~s", [Word, CmdStr]);
fmt_error({expected_subcmd, CmdStr}) ->
    io_lib:format("expected subcommand to ~s", [CmdStr]);
fmt_error({unknown_param, CmdStr, Param}) ->
    io_lib:format("unrecognized parameter \"~s\" to ~s", [Param, CmdStr]);
fmt_error({opt_needs_argument, CmdStr, Opt}) ->
    io_lib:format("option ~s to ~s needs an argument", [Opt, CmdStr]);
fmt_error({opt_already_given, CmdStr, Opt}) ->
    io_lib:format("option ~s is already given to ~s", [Opt, CmdStr]);
fmt_error({unknown_opt, CmdStr, Opt}) ->
    io_lib:format("unrecognized option \"~s\" to ~s", [Opt, CmdStr]);
fmt_error({expected_opt, CmdStr, Opt}) ->
    io_lib:format("expected option \"~s\" to ~s", [Opt, CmdStr]);
fmt_error({expected_arg, From}) ->
    io_lib:format("expected argument to ~s", [fmt_from(From)]);
fmt_error({missing_args, {arg, _, _} = From, _NArgs}) ->
    io_lib:format("expected ~s", [fmt_from(From)]);
fmt_error({missing_args, From, _NArgs}) ->
    io_lib:format("expected argument to ~s", [fmt_from(From)]);
fmt_error({bad_arg, From, {Arg, _Type}}) ->
    io_lib:format("bad value \"~s\" for ~s", [Arg, fmt_from(From)]);
fmt_error(Error) ->
    io_lib:format("~p", [Error]).

fmt_from({cmd, CmdStr}) ->
    ["command ", CmdStr];
fmt_from({opt, short, #{short := Ch}}) ->
    ["option -", Ch];
fmt_from({opt, long, #{long := Str}}) ->
    ["option --", Str];
fmt_from({arg, A, CmdStr}) ->
    ["argument ", A, " to command ", CmdStr].


%%% Completion

is_completion(Env) ->
    case Env of
        {_, #{'_comp_word' := _}} ->
            true;
        _ ->
            false
    end.

get_comp_word(Env) ->
    case Env of
        {_, #{'_comp_word' := CompWord}} ->
            CompWord;
        _ ->
            false
    end.

print_suggestions({{Cmd, ParseOpts}, _CmdStack, ResultOpts, _ResultArgs}) ->
    #{'_comp_word' := CompWord} = ParseOpts,
    AllSuggestions =
        lists:sort(suggested_subcommands(maps:get(cmds, Cmd, []))) ++
        lists:sort(suggested_options(maps:get(opts, Cmd, []), ResultOpts)),
    Suggestions =
        if CompWord == undefined ->
                %% this means that the user hit <tab> after a space
                AllSuggestions;
           true ->
                %% this means that the user hit <tab> right after CompWord
                [S || S <- AllSuggestions,
                      lists:prefix(CompWord, S)]
        end,
    lists:foreach(
      fun(S) ->
              io:put_chars([S, "\n"])
      end, Suggestions).

print_special_suggestion(Type) ->
    case Type of
        dir ->
            io:put_chars("__DIR__\n");
        file ->
            io:put_chars("__FILE__\n")
    end.

suggested_options([#{multiple := true} = Opt | T], ResultOpts) ->
    suggest_opt(Opt, T, ResultOpts);
suggested_options([#{name := Name} = Opt | T], ResultOpts) ->
    case maps:is_key(Name, ResultOpts) of
        true ->
            suggested_options(T, ResultOpts);
        false ->
            suggest_opt(Opt, T, ResultOpts)
    end;
suggested_options([{group, _, Opts} | T], ResultOpts) ->
    suggested_options(Opts ++ T, ResultOpts);
suggested_options([], _) ->
    [].

suggest_opt(Opt, T, ResultOpts) ->
    case Opt of
        #{short := Ch, long := Long, type := boolean} ->
            [[$-, Ch], [$-, $- | Long], [$-, $-, $n, $o, $- | Long] |
             suggested_options(T, ResultOpts)];
        #{short := Ch, long := Long} ->
            [[$-, Ch], [$-, $- | Long] | suggested_options(T, ResultOpts)];
        #{short := Ch} ->
            [[$-, Ch] | suggested_options(T, ResultOpts)];
        #{long := Long, type := boolean} ->
            [[$-, $- | Long], [$-, $-, $n, $o, $- | Long] |
             suggested_options(T, ResultOpts)];
        #{long := Long} ->
            [[$-, $- | Long] | suggested_options(T, ResultOpts)]
    end.

suggested_subcommands([#{cmd := Cmd} | T]) ->
    [Cmd | suggested_subcommands(T)];
suggested_subcommands([{group, _, Cmds} | T]) ->
    suggested_subcommands(Cmds ++ T);
suggested_subcommands([]) ->
    [].

print_completion_script(Cmd, bash) ->
    AbsName = filename:absname(hd(init:get_plain_arguments())),
    io:format("_~s() {\n"
              "  COMPREPLY=($(COMP_LAST_WORD=${COMP_WORDS[COMP_CWORD]} "
              "~s ${COMP_WORDS[@]}))\n"
              "  if [ \"${COMPREPLY[0]}\" == \"__DIR__\" ]; then\n"
              "    compopt -o dirnames\n"
              "    COMPREPLY=(\"${COMPREPLY[@]:1}\")\n"
              "  elif [ \"${COMPREPLY[0]}\" == \"__FILE__\" ]; then\n"
              "    compopt -o default\n"
              "    COMPREPLY=(\"${COMPREPLY[@]:1}\")\n"
              "  fi\n"
              "  return 0\n"
              "}\n"
              "\n"
              "complete -o nosort -F _~s ~s\n",
              [Cmd, AbsName, Cmd, Cmd]);
print_completion_script(Cmd, zsh) ->
    AbsName = filename:absname(hd(init:get_plain_arguments())),
    io:format("_~s() {\n"
              "  sugg=(\"${(@f)$(COMP_LAST_WORD=${words[-1]} ~s $words)}\")\n"
              "  if [ \"${sugg[1]}\" = \"__DIR__\" ]; then\n"
              "    _path_files -/\n"
              "  elif [ \"${sugg[1]}\" = \"__FILE__\" ]; then\n"
              "    _path_files -f\n"
              "  else\n"
              "    compadd -V unsorted -a sugg\n"
              "  fi\n"
              "  return 0\n"
              "}\n"
              "\n"
              "compdef _~s ~s\n",
              [Cmd, AbsName, Cmd, Cmd]);
print_completion_script(_, _) ->
    io:put_chars("Unknown shell - cannot generate completion script\n"),
    halt(1).

try_detect_shell() ->
    case os:getenv("SHELL") of
        false ->
            unknown;
        SHELL ->
            case filename:basename(SHELL) of
                "bash" -> bash;
                "zsh" -> zsh;
                _ -> unknown
            end
    end.
