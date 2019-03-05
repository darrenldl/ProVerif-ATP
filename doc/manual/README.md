# ProVerif-ATP user manual

pvatp is the main executable that handles the entire workflow

To start, simply type

```bash
pvatp protocol.pv
```

where `protocol.pv` is the protocol ProVerif specification file

Following shows an example that also demonstrates basic navigation in Narrator, see [here](narrator.md) for a more complete guide on using the Narrator interface

## Example

We pick CH07 as our example (stored as `examples/CH07-tag-auth.pv`)

We first go through the specification and our encoding, then we'll use pvatp for our analysis

#### CH07 specification

CH07 is a RFID protocol for mutual authentication between a reader and a tag

![ch07_chart](ch07_chart.png)

Above shows the CH07 specification as a message sequence chart, which is a commonly used informal notation for outlining the major protocol steps.

At top left and top right, R and T denotes the RFID reader and the RFID tag respectively. The "k, ID" above them indicates they both share common secrets k, ID prior to the run (execution) of the protocol. k denotes a key and ID denotes an identifier (e.g. serial number).

At the beginning, R generates a nonce (randomly generated number that is used only once) r1 then sends it to T. T generates a nonce r2, calculates $\tilde{g}$ and $ID2$

#### CH07 encoding

#### Using pvatp

invoke pvatp on the `.pv` file, pvatp handles everything onward automatically as seen by the following sample terminal output

```bash
$ pvatp CH07-tag-auth.pv

ProVerif - Reprint
Reprinted version of your file is stored as :
    examples/CH07-tag-auth.pv.reprinted

ProVerif - Translate to TPTP
Note that certain syntactic modifications are required for the
translation to work, they are done by ProVerif automatically

The processed version of syntax tree is stored as :
    examples/CH07-tag-auth.pv.processed
The TPTP file is stored as :
    examples/CH07-tag-auth.p

Calling Vampire to solve the TPTP file
The output of Vampire is stored as :
    /home/darren/ProVerif-ATP/CH07-tag-auth.solver_log
Generating Narrator interface of the output file
Opening Narrator interface in browser
```

Below shows the Narrator interface opened by pvatp

![narrator_init](narrator_init.png)

**Demo site** You can also access the Narrator interface with CH07 files loaded through [here](https://darrenldl.gitlab.io/narrator-ch07), it is the same as the one you get locally through pvatp

There are three major modes in Narrator which we will go through one at a time. This initial interface shows the Narrator's "Tagged ProVerif source + attack trace" mode, which displays a prettified and tagged version of the ProVerif source code on left, and the attack trace on bottom right panel.

The tagged version uses same style to annotated input and output steps as the attack trace for easy navigation, but comments and original syntax styles are not preserved.

Top right shows the control panel, the same panel is used for all modes. We can switch to other modes through this panel. By clicking "Show raw ProVerif code + attack trace", we can switch to Narrator's "Raw ProVerif source + attack trace mode". This displays the raw ProVerif code on left instead of the prettified version as shown below.

![narrator_raw_pv](narrator_raw_pv.png)

This mode is mainly useful when you need to view the actual raw ProVerif code for debugging your specification or if you feel Narrator is incorrect etc.

Finally we click "Show knowledge graph" which invokes the knowledge graph mode as shown below

![Narrator knowledge graph](narrator_knowledge.png)

The knowledge graph display is an interactive, zoomable display. Recall from the attack trace shown in the attack trace mode (copied below)

```ocaml
1.    sess_1.1    sess_1 -> I : r1_s1

2.    sess_1.2    sess_1 -> I : tuple_2(r2_s1,split_L(xor(rotate(ID,h(xor(xor(r1_s1,r2_s1),k))),h(xor(xor(r1_s1,r2_s1),k)))))

3.    R.1         R -> I : tuple_2(QUERY,r1)

4.    R.3         I -> R : tuple_2(X28,split_L(xor(rotate(ID,h(xor(xor(r1,X28),k))),h(xor(xor(r1,X28),k)))))

5.    R.3         R -> I : objective
```

we know step 4 (or step `R.3 I -> R`, which indicates the input step prior to output step 3 in R) is when the attacker provides the message `tuple_2(X28,split_L(xor(rotate(ID,h(xor(xor(r1,X28),k))),h(xor(xor(r1,X28),k)))))` and obtains objective at step 4 (or step `R.3 R -> I`, which indicates the output step 3 in R).
