#!/bin/bash

source problem_list.sh

for f in ${files[@]}; do
  ./solve.sh $f
done
