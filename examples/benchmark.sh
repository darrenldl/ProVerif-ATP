#!/bin/bash

in_file=$1

f=$(echo $in_file | sed "s/\.pv//")

total_mem_in_KB=$(grep MemTotal /proc/meminfo | awk '{ print $2 }')
total_mem_in_MB=$[total_mem_in_KB / 1024]
time=$[24 * 60 * 60]

echo "Benchmarking ""$f".pv

proverif -in pitype -log-pv-only "$f".pv >/dev/null
mv "$f".pv.export "$f".pv.reprinted
proverif -in pitype -out tptp -tag-in-out -log-pv -o "$f".p "$f".pv >/dev/null
mv "$f".pv.export "$f".pv.processed

vampire -t "$time"s -m $[total_mem_in_MB-500] "$f".p -p tptp > "$f".bench_log

time=$(grep "Time" "$f".bench_log | awk '{print $4}')

# remove the first 3 lines
# tail -n +4 "$f".bench_log > "$f".solver_log.1
# remove the last 17 lines
# head -n -17 "$f".solver_log.1 > "$f".solver_log
# rm "$f".solver_log.1

echo "$f, $time" >> benchmark_total
