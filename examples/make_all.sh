#!/bin/bash

date=$(date +"%Y-%m-%d_%H%M")

for f in *.pv; do
  echo "Testing" $f
  ./make.sh $f $1
done
