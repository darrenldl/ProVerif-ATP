#!/bin/bash

in_file=$1

f=$(echo $in_file | sed "s/\.pv//")

total_mem_in_KB=$(grep MemTotal /proc/meminfo | awk '{ print $2 }')
total_mem_in_MB=$[total_mem_in_KB / 1024]
time=$[24 * 60 * 60]

echo "Solving ""$f".pv

proverif -in pitype -log-pv-only "$f".pv >/dev/null
mv "$f".pv.export "$f".pv.reprinted
proverif -in pitype -out tptp -tag-in-out -log-pv -o "$f".p "$f".pv >/dev/null
mv "$f".pv.export "$f".pv.processed

vampire -t "$time"s -m $[total_mem_in_MB-500] "$f".p --proof_extra full -stat none > "$f".solver_log

