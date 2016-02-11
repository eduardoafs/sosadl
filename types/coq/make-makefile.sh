#!/bin/sh

( echo '-R SosADL SosADL '; find . -name '*.v' -print | sort -r ) | tee _CoqProject | xargs coq_makefile > Makefile

# coq_makefile -f _CoqProject > Makefile
