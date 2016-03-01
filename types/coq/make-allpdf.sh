#!/bin/sh

rm all.pdf
make -j2 && make 'COQDOCLIBS=-p "\usepackage{listings}"' all.pdf
