#!/bin/bash

# Example: ./runTest.sh test/UnfoldTest.hs

#"-fexternal-interpreter -prof" \

[[ -n "$1" ]] && stack ghci --ghci-options="-isrc -isrc/programs -itest -iutils $1 +RTS -M2G" || echo "Requires path to the test file!"
