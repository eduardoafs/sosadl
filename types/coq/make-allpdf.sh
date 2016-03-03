#!/bin/sh

rm -f all.pdf
make -j2 &&
    find SosADL -name '*.v' | xargs coqdep -c -sort -suffix .v | xargs coqdoc -toc -interpolate -utf8 -latex -p "\usepackage{listings}" -o all.tex &&
    latexmk -pdf all.tex

