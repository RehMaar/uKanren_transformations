#!/bin/bash

# $1 -- seconds
# $2 -- command
# $3 -- check until 

sec=$1
cmd="$2"
bound=$3

[[ -z "$sec" || -z "$cmd" || -z "$bound" ]] && echo "Need to set all parameters" && exit

echo "> Amount of seconds:"  $sec
echo "> Command to run:" "$cmd"
echo "> Check first:" $bound "natural numbers"

parallel "timeout $sec $cmd" <<< $(seq 1 $bound)
