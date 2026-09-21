#!/bin/bash
set -euo pipefail
cd $(dirname $0)

echo "-R src coind" >_CoqProject
find src | grep ".v$" >>_CoqProject
rocq makefile -f _CoqProject -o Makefile
make
