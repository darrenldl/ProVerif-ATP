#!/bin/bash

rm -f benchmark_total

source problem_list.sh

for f in ${files[@]}; do
  ./benchmark.sh $f
done
