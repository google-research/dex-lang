#/usr/bin/env bash

_dex_completions()
{
    COMPREPLY=();
    local word="${COMP_WORDS[COMP_CWORD]}";
    if [ "$COMP_CWORD" -eq 1 ]; then
        COMPREPLY=($(compgen -W "repl script web watch" -- "$word"));
    else
        COMPREPLY=()
    fi
}
complete -o default -F _dex_completions dex
