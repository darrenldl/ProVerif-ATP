# Using Narrator in software

In the current suite and in our project, we use the `pvatp` main executable to streamline the entire operation, however, Narrator is not heavily tied to `pvatp` and can be attached to other pieces of software quite easily.

The Narrator runtime consists of a set of Javascript files and a HTML file. This can be observed after building narrator (i.e. via `make narrator`) in the `build/pvatp_assets/narrator/` directory. Following shows the output of `ls`.

```bash
$ ls -1 build/pvatp_assets/narrator/
file_strings.js
index.html
narrator.bc.js
narrator.bc.runtime.js
node_modules
```

## Explanation of the runtime files

- `file_strings.js`

  - The content ProVerif protocol specification file (.pv) and output of Vampire (.solver_log) are embedded here by putting the entire file inside a variable

  - More specifically, variable `pvFile` would contain the entirety of the .pv file, variable `tptpFile` would contain the entirety of the .solver_log file

  - The content of a fresh `file_strings.js` is just

    - ```javascript
      var pvFile = ""
      
      var tptpFile = ""
      ```

    - `pvatp` simply replaces the the values of above variables with actual file content

- `index.html`

  - This is the HTML file to be opened by browser

  - All Javascript files required are loaded by this HTML file

- `narrator.bc.js`, `narrator.bc.runtime.js`

  - These are the Javscript files compiled from Narrator's OCaml source code using `Js_of_ocaml`

- `node_modules`

  - These are a set of Javascript libraries used by Narrator

  - They are downloaded originally through `npm`

## How pvatp uses the files

A copy of the runtime files are stored as the `pvatp_assets/narrator/` folder

At each run, `pvatp` simply copies the entire `narrator` folder to a temporary location (i.e. `/tmp/` on most Linux systems), replaces `file_strings.js` with variable declarations containing file content, then launches the default web browser with URL pointing to the HTML file (e.g. `file:///tmp/narrator/index.html`).

If you would like to use Narrator in your software, you can follow the above approach. `pvatp`'s source code (stored as `src/pvatp.py`) is very straightforward to examine as well.
