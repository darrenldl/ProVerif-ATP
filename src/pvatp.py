#!/usr/bin/env python3
import sys
import os
import subprocess
import shutil
import tempfile
import webbrowser

script_path = sys.path[0]
asset_path  = os.path.join(script_path, "pvatp_assets")

local_proverif_path = os.path.join(asset_path, "proverif")
local_vampire_path  = os.path.join(asset_path, "vampire")
local_narrator_path = os.path.join(asset_path, "narrator")

if not os.path.isfile(local_proverif_path):
  print("ProVerif binary not detected in script directory")
  exit(1)

if not os.path.isfile(local_vampire_path):
  print("Vampire binary not detected in script directory")
  exit(1)

if len(sys.argv) == 1:
  print("Usage : pvatp.py file.pv")
  exit(0)
elif len(sys.argv) > 2:
  print("Too many arguments")
  exit(1)

full_input_path = sys.argv[1]

if not os.path.isfile(full_input_path):
  print("File does not exist or is not a regular file")
  exit(1)

input_dir_path              = os.path.dirname(full_input_path)
input_file                  = os.path.basename(sys.argv[1])
input_file_without_ext      = os.path.splitext(input_file)[0]
full_input_path_without_ext = os.path.join(input_dir_path, input_file_without_ext)

tptp_output_path      = full_input_path_without_ext + ".p"

export_path           = full_input_path + ".export"
reprinted_path        = full_input_path + ".reprinted"
processed_path        = full_input_path + ".processed"

solver_log_name        = input_file_without_ext + ".solver_log"
solver_log_output_path = os.path.join(os.getcwd(), solver_log_name)

if os.path.isfile(solver_log_output_path):
  print("Found solver log " + solver_log_output_path)
  print("Do you want to proceed with the solver log? y/n ", end='')
  choice = input().lower()
  if choice == "y":
    process_files=False
  else:
    process_files=True
else:
  process_files=True

if process_files:
  print("")
  print("ProVerif - Reprint")
  try:
    subprocess.run([local_proverif_path, "-in", "pitype", "-log-pv-only", full_input_path], check=True, capture_output=True)
  except subprocess.CalledProcessError as e:
    print("pvatp : ProVerif indicated an error, output is shown below")
    print("")
    print(e.stdout.decode("utf-8"))
    exit(1)

  os.rename(export_path, reprinted_path)
  print("Reprinted version of your file is stored as :")
  print("    " + reprinted_path)

  print("")

  print("ProVerif - Translate to TPTP")
  try:
    subprocess.run([local_proverif_path, "-in", "pitype", "-out", "tptp", "-log-pv", "-tag-in-out", "-o", tptp_output_path, full_input_path], check=True, capture_output=True)
  except subprocess.CalledProcessError as e:
    print("pvatp : ProVerif indicated an error, output is shown below")
    print("")
    print(e.stdout.decode("utf-8"))
    exit(1)

  os.rename(export_path, processed_path)

  print("Note that certain syntactic modifications are required for the")
  print("translation to work, they are done by ProVerif automatically")
  print("")
  print("The processed version of syntax tree is stored as :")
  print("    " + processed_path)
  print("The TPTP file is stored as :")
  print("    " + tptp_output_path)

  print("")

  print("Calling Vampire to solve the TPTP file")
  print("The output of Vampire is stored as :")
  print("    " + solver_log_output_path)
  with open(solver_log_output_path, "w") as log_output:
    subprocess.run([local_vampire_path, "-t", "86400", "-stat", "none", "-p", "tptp", tptp_output_path], stdout=log_output)

print("Generating Narrator interface of the output file")
temp_dir = tempfile.gettempdir()
dst_narrator_path = os.path.join(temp_dir, "narrator")
dst_html_path     = os.path.join(dst_narrator_path, "index.html")

# create a copy of Narrator in the temporary directory
shutil.rmtree(dst_narrator_path, ignore_errors=True)
shutil.copytree(local_narrator_path, dst_narrator_path)

# update file_strings.js to include the ProVerif file and TPTP file
file_strings_js_path = os.path.join(dst_narrator_path, "file_strings.js")

os.remove(file_strings_js_path)
with open(file_strings_js_path, "wb") as out_file:
  with open(full_input_path, "rb") as in_file:
    out_file.write(b"var pvFile = `")
    out_file.write(in_file.read())
    out_file.write(b"`")

  out_file.write(b"\n")

  with open(solver_log_output_path, "rb") as in_file:
    out_file.write(b"var tptpFile = `")
    out_file.write(in_file.read())
    out_file.write(b"`")

print("Opening Narrator interface in browser")
webbrowser.open("file://" + dst_html_path)

