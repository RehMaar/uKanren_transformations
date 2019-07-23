#!/bin/bash


[[ -n "$1" ]] && stack ghci --ghci-options="-isrc -isrc/programs -itest -iutils $1" \
			  || echo "Requires path to the test file!"
