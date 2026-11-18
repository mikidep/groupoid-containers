#!/usr/bin/env sh

printf 'module Everything where\n\n'
find Cubical/ -type f -name "*.agda" \
  | sort \
  | grep -Fv '_' \
  | grep -Fv '/Coherence' \
  | sed -e 's/\//./g' -e 's/\.agda$//g' -e 's/^/import /'
