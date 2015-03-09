#!/bin/sh

( echo '-R tests tests'; find . -name '*.v' -print | sort -r ) | xargs coq_makefile > Makefile

# coq_makefile -f _CoqProject > Makefile
