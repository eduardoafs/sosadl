#!/bin/sh

rm -f all.pdf
make -j2 &&
    find SosADL -name '*.v' | xargs coqdep -c -sort -suffix .v | xargs coqdoc -toc -interpolate -utf8 -latex -p "\usepackage{listings}" -o all.tex &&
    sed -i.bak -e 's/\\usepackage{coqdoc}/\\usepackage[color]{coqdoc}/' all.tex &&
    latexmk -pdf all.tex

