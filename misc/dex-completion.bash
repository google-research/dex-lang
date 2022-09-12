#/usr/bin/env bash

_dex_completions()
{
    COMPREPLY=();
    local word="${COMP_WORDS[COMP_CWORD]}";
    if [ "$COMP_CWORD" -eq 1 ]; then
        COMPREPLY=($(compgen -W "repl script web watch" -- "$word"));
    elif [ "${COMP_WORDS[1]}" = "repl" ]; then
        COMPREPLY=()
    elif [ "${COMP_WORDS[1]}" = "script" ]; then
        COMPREPLY=($(compgen -G "*.dx" -- "$word"));
    elif [ "${COMP_WORDS[1]}" = "watch" ]; then
        COMPREPLY=($(compgen -G "*.dx" -- "$word"));
    elif [ "${COMP_WORDS[1]}" = "web" ]; then
        COMPREPLY=($(compgen -G "*.dx" -- "$word"));
    else
        COMPREPLY=()
    fi
}
complete -F _dex_completions dex
