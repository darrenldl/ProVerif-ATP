# ProVerif-ATP

Combining ProVerif and Automated Theorem Provers for Security Protocol Verification

Authors : [Di Long Li](https://github.com/darrenldl) and Alwen Tiu, at The Australian National University, Canberra ACT 2600, Australia

## Installation

The prerequisites and install command are documented [here](INSTALL.md)

## Basic usage

`pvatp protocol.pv`

where `protocol.pv` is the protocol specification in typed pi-calculus used by ProVerif

`examples/` directory contains the protocol specifications we used for our benchmark, and also other ones we created during the project

See the [user manual](doc/manual/README.md) for more details and an example

## Documentation

- `doc/manual/` ([README](doc/manual/README.md)) contains the user manual

- `doc/pvatp/` ([README](doc/pvatp/README.md)) contains the documentations detailing the architecture of ProVerif-ATP

- `doc/proverif/` ([README](doc/proverif/README.md)) contains the documentations detailing the modifications we made in ProVerif

- `doc/narrator/` ([README](doc/narrator/README.md)) contains the documentations detailing architecture or Narrator

## Paper
This project was accepted for CADE-27.
The pre-printed copy with appendix is available in this repository here [here](paper/CADE-27_paper-42_Di_Long_Li_and_Alwen_Tiu_full.pdf).

The final authenticated publication is available online at [https://doi.org/10.1007/978-3-030-29436-6\_21](https://doi.org/10.1007/978-3-030-29436-6_21)

## Index and licenses

- `src/`

  - This contains the main Python script which invokes the following tools to deliver a streamlined user experience. The files inside are published under the MIT license.

- `narrator/`

  - This is part of the original work developed for this project (excluding `node_modules/` subdirectory). Narrator provides the interface for viewing the knowledge graph and attack traces. The files (excluding `node_modules/` subdirectory) are published under the MIT license.

  - The subdirectory `node_modules/` contains downloaded copies of Javascript libraries. They are included in the repository for easier building and usage of the framework only. They are not part of our work, they are not modified by us, and are distrbuted under their respective original licenses.

- `proverif2.00/`

  - This is a modified copy of ProVerif version 2.00. We intend to submit the modifications to the original authors for integrations later on. We license our modifications using the [exact same GPL license](http://prosecco.gforge.inria.fr/personal/bblanche/proverif/LICENSEGPL) used by ProVerif 2.00.
  - However, please note that this is not the final copy we intend to submit to the authors, as we are not completely certain if all modifications are actually safe, and we will need to discuss with the authors prior to submitting any patches etc.

- `examples/`

  - This contains all the protocol specification and related files used in the benchmark

## Versioning

- We follow the semantic versioning scheme with the following specifics

  - Right now

    - Any change in our copy of ProVerif will result in increment of the version number of ProVerif-ATP (following the semantic versioning scheme's guidelines)

    - Narrator's versioning is always same as ProVerif-ATP's versioning

    - This means if there are changes in our copy of ProVerif, but not in Narrator, both ProVerif-ATP and Narrator's version numbers are still incremented

  - In future after the modifications have been integrated into the official ProVerif distribution

    - Narrator's versioning will still be always same as ProVerif-ATP's versioning

- We tag each new version when the version is finalised and released

## Changelog

- All changes are logged under the same [changelog](CHANGELOG.md)
  - Changes in different components are documented separately as different sections

## Acknowledgement

While the TPTP parser code in Narrator was independently developed from scratch according to the [TPTP syntax reference](http://tptp.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html), [zipperposition](https://github.com/c-cube/zipperposition)'s TPTP parser code was used as reference during the final debugging phase
