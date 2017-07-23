#!/bin/sh
isabelle build -c ICL

# Overwrite report.pdf with the latest compiled version.
cp -f output/document.pdf report.pdf
