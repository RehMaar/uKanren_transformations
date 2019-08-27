#!/bin/bash

# $1 -- upper bound for execution in seconds
# $2 -- command to execute
# $3 -- upper bound of checking

sec=$1
cmd="$2"
bound=$3

[[ -z "$sec" || -z "$cmd" || -z "$bound" ]] && echo "Need to set all parameters: <$0 sec cmd upper_bound>" && exit

echo "> Amount of seconds:"  $sec
echo "> Command to run:" "$cmd"
echo "> Check first:" $bound "natural numbers"

parallel "timeout $sec $cmd" <<< $(seq 1 $bound)
