# ProVerif-ATP installation guide

## Prerequisites

#### Platform

- The software suite was used largely on the Linux platform. While all components should compile on Windows and Mac, the Makefile and various bash scripts may not function as intended on those platforms.

#### System binaries required

- `wget` (optional)
  - The Makefile will try to download a copy of Vampire if the archive is not present. You can download the archive manually and place it in the repository root directory to skip this. See below for details.

#### Compilers required

- OCaml compiler >= 4.07.1 (for Narrator and ProVerif)

  - You can switch to 4.07.1 by `opam switch 4.07.1`

- C++ compiler (for Vampire)

- Python >= 3.7.2 (for pvatp.py)

#### OCaml packages required

OCaml packages are easiest to install via the use of the `opam` tool, which should be available on most distros

- For Narrator

  - `dune`

  - `mparser`

  - `core_kernel`

  - `js_of_ocaml`

  - `js_of_ocaml-ppx`

  - `js_of_ocaml-lwt`

  - `lwt`

  - `lwt_ppx`

  - `menhir`

- For ProVerif

  - `ocamlfind`

  - `ocamlbuild`

  - `lablgtk`

#### Notes

- As per Vampire's [license](https://vprover.github.io/licence.html), we are not allowed to redistribute the sources of Vampire, thus we do not bundle it in this repository
  - The Makefile will try to download the file automatically via the HTTPS URL if `4.2.2.tar.gz` is not present

  - If you feel this is unsafe, you can download the archive manually [here](https://github.com/vprover/vampire/releases/tag/4.2.2), and rename it to `4.2.2.tar.gz` and place it in the repository root directory (where Makefile resides in)

## Command

Simply type

```bash
make install
```

to build and install the software suite to `/usr/local/bin/`

If you only want to build, then just type

```bash
make
```

For both cases, the built files are stored in `build/` directory at the repository's root (where the Makefile is)

To install the files manually, move both `build/pvatp` and `build/pvatp_assets/` to the desired location. Note that both the file and the folder need to be in the same directory.

#### Notes

- The installed files will appear as `/usr/local/bin/pvatp` (main executable) and `/usr/local/bin/pvatp_assets/` (files required by the main executable)

- `pvatp` only accesses the copies of ProVerif and Vampire in `/usr/local/bin/pvatp_assets/`, so there is no need to remove prior installation of ProVerif or Vampire in your system

- More generally, `pvatp` accesses the `pvatp_assets/` folder at where it is stored, so you can relocate the files as long as both `pvatp` and `pvatp_assets/` reside in the same directory
