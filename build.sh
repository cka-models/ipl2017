#!/bin/sh
isabelle build -c -b ICL

# Overwrite document.pdf with the latest version.
cp output/document.pdf document.pdf
