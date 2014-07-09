#!/bin/sh

make && make 'COQDOCLIBS=-p "\usepackage{listings}"' all.pdf
