#!/bin/bash

set -e

DIR="$(dirname "$BASH_SOURCE[0]")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/All.thy")
else
    FILES=()
fi

SESSION=HOL-Analysis
#SESSION=Lots-Of-Stuff

ISABELLE_DIR=/opt/Isabelle2021

"$ISABELLE_DIR/bin/isabelle" jedit -l "$SESSION" -d . "${FILES[@]}" "$ISABELLE_DIR/src/Pure/ROOT.ML" "$@" &
