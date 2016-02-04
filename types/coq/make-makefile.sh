#!/bin/sh

( echo '-R SosADL SosADL '; find . -name '*.v' -print | sort -r ) | xargs coq_makefile > Makefile

# coq_makefile -f _CoqProject > Makefile
