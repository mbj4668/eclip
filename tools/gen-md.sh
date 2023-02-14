#!/bin/sh

### Generates markdown for exported types and functions from an erlang
### module.
###
### A type must be specified as:
###
###   <type description as comments>
###   -type NAME ...
###
### A function must be specified as:
###   
###   -spec NAME ...
###   <function description as comments>
###   NAME( ...
###
### The type and spec bodies are extracted verbatim, including
### comments, which means that comments are used to document the types
### and functions.
###
### edoc isn't used since it doesn't support documentation of types.
extract_exported() {
    cat $1 | awk -v WHAT=$2 '
    function print_exported(str) {
        # split on xxx/ (all end up in seps)
        split(str, a, "[a-z_]+/[0-9]+", seps);
        for (j in seps) {
            # print xxx
            if (WHAT == "export") {
                print seps[j];
            } else {
                print gensub("/.*", "", 1, seps[j]);
            }
        }
        if (str ~ "]\\).") {
            skip = 1;
        }
    }
    
    BEGIN {
        skip = 1;
    }
    
    $0 ~ ("^-" WHAT "\\(") {
        skip = 0;
        print_exported($0)
        next;
    }
    skip == 0 {
        print_exported($0)
    }
'
}

extract_def() {
    cat $1 | awk -v $2=$3 '
    ### Extract the given Erlang type or function definition, and
    ### convert all type references to relative links.

    function colorize_comment(str) {
        sub("%.*", "<span style=\"color:indianred\">&</span>", str);
        return str;
    }
    
    function print_with_links(str) {
        ## convert all type references to links
        split(str, a, "[a-z_]+\\([^\\).]?\\)", seps);
        i = 1
        for (j in seps) {
            printf("%s", a[i]);
            if (seps[j] in builtins) {
                printf("%s", seps[j]);
            } else {
                printf("<a href=\"#type_%s\">%s</a>",
                       gensub("\\(.*", "", 1, seps[j]),
                       seps[j]);
            }
    
            i++;
        }
        print a[i];
    }
    
    BEGIN {
        skip = 1;
        k = 1;
    
        if (FUNC != "") {
            split(FUNC, a, "/")
            FNAME = a[1]
            ARITY = a[2]
        }
    
        builtins["string()"] = 1
        builtins["integer()"] = 1
        builtins["pos_integer()"] = 1
        builtins["float()"] = 1
        builtins["boolean()"] = 1
        builtins["term()"] = 1
        builtins["fun()"] = 1
        builtins["atom()"] = 1
        builtins["char()"] = 1
        builtins["iodata()"] = 1
    
    }
    
    ## special annotation for multi-arity functions
    $0 ~ ("^%% @" FNAME "/" ARITY) {
       found_func = 1;
       next;
    }

    $0 ~ ("%% @" FNAME "/") {
       ## this is NOT our function!
       getline; next;
    }

    print_comments == 1 && /^%%/ {
        sub("^%+", "");
        sub("^(\\s)+", "");
        $0 = colorize_comment($0);
        print_with_links($0);
        next;
    }

    ## keep track of comments.  we use them if they are right above the
    ## type we are extracting
    skip == 1 && /^%%/ {
        comments[k] = $0;
        k++;
        next;
    }
    
    ## this is the type we are looking for
    $0 ~ ("^-type " TYPE "\\(") {
        skip = 0;
        printf("### <a name=\"type_%s\">%s</a>\n\n",
               gensub("\\(.*", "", 1, $2),
               $2);
        for (c in comments) {
            print gensub("^(\\s)+", "", 1, gensub("^%+", "", 1, comments[c]));
        }
        for (c in comments) {
            delete comments[c]
        }
        printf("<pre><code>");
        $0 = colorize_comment($0);
        print_with_links($0);
        if (($0 ~ "\\.$") && !($0 ~ "%")) {
            ## end of the type
            skip = 1;
            printf("</code></pre>\n");
        }
    
        next;
    }
    
    ## this is the function we are looking for
    found_func == 1 || $0 ~ ("^-spec " FNAME "\\(") {
        found_func = 0;
        skip = 0;
        printf("### <a name=\"func_%s\">%s/%s</a>\n\n", FNAME, FNAME, ARITY);
        for (c in comments) {
            delete comments[c]
        }
        printf("<pre><code>");
        print_with_links($0);
        if (($0 ~ "\\.$") && !($0 ~ "%")) {
            ## end of function spec
            skip = 1;
            print_comments = 1;
            printf("</code></pre>\n");
        }

        next;
    }
    
    ## if we end up here we delete all comments collected so far
    {
        for (c in comments) {
            delete comments[c]
        }
    }
    
    ## end of the type
    skip == 0 && TYPE != "" && /\.$/ {
        $0 = colorize_comment($0);
        print_with_links($0);
        if ($0 ~ "%") { # comment line that ends with "." -  keep going
            next;
        }
        skip = 1;
        printf("</code></pre>\n");
        next;
    }
    
    ## end of the function spec
    skip == 0 && FUNC != "" && /\.$/ {
        $0 = colorize_comment($0);
        print_with_links($0);
        if ($0 ~ "%") { # comment line that ends with "." -  keep going
            next;
        }
        print_comments = 1;
        skip = 1;
        printf("</code></pre>\n");
        next;
    }
    
    ## end of comments between -spec and function definition
    print_comments == 1 && $0 ~ ("^" FNAME "\\(") {
        print_comments = 0;
        skip = 1;
    }

    ## body of the type
    skip == 0 {
        ## put color on all comments
        $0 = colorize_comment($0);
        print_with_links($0);
    }
    { next; }
'

}

extract_mod() {
    cat $1 | awk '
    ### Extract the module name

    /^-module/ { print gensub("^-module\\(([a-z]*)\\).*", "\\1", 1); exit 0; }
'
}


extract_mod_descr() {
    cat $1 | awk '
    ### Extract the module description, which is the text in comments
    ### before the -module declaration.

    /^-module/ { exit 0; }

    { sub("^%+\\s?", ""); print; }
'
}


if  [ $# != 1 ]; then
    echo "Usage: gen-md.sh ERLFILE"
    exit 1
fi

erlfile=$1

echo '# The `'"$(extract_mod $erlfile)"'` module'
echo ""

extract_mod_descr $erlfile

echo "## Types"

for t in $(extract_exported $erlfile export_type);
do
    extract_def $erlfile TYPE $t
    echo ""
done
         
echo "## Functions"

for f in $(extract_exported $erlfile export);
do
    extract_def $erlfile FUNC $f
    echo ""
done
         

