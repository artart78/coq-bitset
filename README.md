# coq-bitset

## Description

The purpose of this library is to help proving bit-level algorithms written in Coq/SSReflect
by providing a trivial conversion from operations over bitsets to finite sets and efficient
proved extraction to Caml.

A paper describing this library has been accepted at FLOPS2016. The version used for the
conference is tagged `flops`.

A documentation of the library can be found [here](https://artart78.github.com/coq-bitset/).

## Installation

### Installing with OPAM (strongly recommended)

Everything can be installed everything by using
[OPAM](https://opam.ocaml.org/doc/Install.html).

You first need to add some coq-related repositories:
```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
```

Then, you need to install coq-bits, the dependencies will be installed automatically:
```shell
opam pin add coq-bits https://github.com/artart78/coq-bits.git
```
(Note you may need to confirm by pressing Y.)

Then, coq-bitset can be installed exactly the same way:
```shell
opam pin add coq-bitset https://github.com/artart78/coq-bitset.git
```

### Installing by hand

You may be able to install the library by hand, although it has not been tested.

The dependencies are:
  + Coq 8.5~beta2 (other versions are untested)
  + SSReflect & Mathcomp 1.5.1~beta2 (other versions are untested)
  + [coq-bits](https://github.com/artart78/coq-bits)

Then, just doing the usual:
```shell
make
make install
```
should work.

## Usage

In order to import the library, simply use:
```Coq
From Bitset
  Require Import repr_op.
```

All the operations are detailed in src/extractions/axioms*.v in the coq-bits repository.

Then, the relation between finite sets and bitsets is defined as:
```Coq
machine_repr: Int -> {set 'I_wordsize} -> Prop.
```

Depending on your program, you may have to prove validity by proving a machine_repr relation, or an equality.

All of them can by proved by using the lemmas in src/repr_op.v from this repository, using the OP_repr lemmas,
where OP is an "high-level" operation defined in the file using bitset operations (for example: get for getting
a bit, inter for computing the intersection, etc.).
