#!/bin/bash

insert_lines() {
    i=0
    while read p; do
        offset=$[$i + $3]
        sed -i "$offset i \ $p" $2
        i=$i+1
    done <$1
}

in_file=$(echo "$1" | sed "s/\.pv//")

rm -f "$in_file.p"

if [[ "$2" == "spass" ]]; then
  rm -f "$in_file.spass"

  proverif -in pitype -out spass -tag-in-out -o "$in_file.spass" "$in_file.pv"

  if [ -f "$in_file.spass" ]; then
    dfg2tptp "$in_file.spass" "$in_file.p"
  fi
else
  proverif -in pitype -log-pv-only "$in_file.pv"
  mv "$in_file.pv.export" "$in_file.pv.reprinted"
  proverif -in pitype -out tptp -tag-in-out -log-pv -o "$in_file.p" "$in_file.pv"
  mv "$in_file.pv.export" "$in_file.pv.processed"
fi

# if [[ $2 != "gen" ]]; then
#   date=$(date +"%Y-%m-%d_%H%M")
#   if [ -f "$in_file.p" ]; then
#     total_mem_in_KB=$(grep MemTotal /proc/meminfo | awk '{ print $2 }')
#     total_mem_in_MB=$[total_mem_in_KB / 1024]
#     time=$[24 * 60 * 60]
#     vampire -t "$time"s -m $[total_mem_in_MB-500] "$in_file.p" -stat none -p tptp --avatar off > vampire_log/"$in_file".vampire."$date".log
#   fi
# fi

