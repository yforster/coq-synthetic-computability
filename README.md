# A Constructive and Synthetic Theory of Reducibility: Myhill’s Isomorphism Theorem and Post’s Problem for Many-one and Truth-table Reducibility in Coq

This is the Coq mechanisation of the paper "A Constructive and Synthetic Theory of Reducibility: Myhill’s Isomorphism Theorem and Post’s Problem for Many-one and Truth-table Reducibility in Coq".

## How to compile the code

You need `The Coq Proof Assistant, version 8.12`, the [`stdpp` library](https://gitlab.mpi-sws.org/iris/stdpp) and the [Equations](https://mattam82.github.io/Coq-Equations/) package installed.

Afterwards, you can type `make`.

## How to install Coq

The easiest way to install Coq and required libraries is via `opam` (version `2`).
```
opam switch create coq-reducibility 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-8.12.1 coq-equations-1.2.3+8.12 coq-stdpp.1.4.0
```
