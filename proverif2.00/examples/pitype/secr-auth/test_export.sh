#!/bin/bash

in_file=$(echo "$1" | sed "s/\.pv//")

proverif -in pitype -log-pv-only $in_file.pv > /dev/null
if [[ $? != 0 ]]; then
  echo "Failed to process original file"
fi

output=$(proverif -in pitype -log-pv-only $in_file.pv.export)
rm -f $in_file.pv.export.export
if [[ $output == "" ]]; then
  echo "Okay"
else
  echo "Not okay"
  echo $output
fi
