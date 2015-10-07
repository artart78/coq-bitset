# coq-bitset

## Description

The purpose of this library is to help proving bit-level algorithms written in Coq/SSReflect
by providing a trivial conversion from operations over bitsets to finite sets and efficient
proved extraction to Caml.

## Installation

### Installing Coq/SSReflect

TODO

### Installing coq-bits

In order to compile this library, you will also need to compile coq-bits.

#### Without OPAM
```shell
git clone https://github.com/artart78/coq-bits.git
cd coq-bits
make
make install # launch as root if needed
```

#### With OPA
```shell
git clone https://github.com/artart78/coq-bits.git
cd coq-bits
opam pin add coq:bits
```
Then you can simply update with:
```shell
opam upgrade coq:bits
```

### Installing coq-bitset

#### Without OPAM
```shell
git clone https://github.com/artart78/coq-bitset.git
cd coq-bitset
make
make install # launch as root if needed
```

#### With OPAM
```shell
git clone https://github.com/artart78/coq-bitset.git
cd coq-bitset
opam pin add coq:bitset
```
Then you can simply update with:
```shell
opam upgrade coq:bitset
```

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
