#! /usr/local/bin/fish

set dexprompt (printf '\x1B[32m\x02>=> \x1B[m\x02')
stack exec dex -- repl --prompt "$dexprompt"

