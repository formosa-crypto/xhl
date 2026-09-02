# XHL — A Coq library of probabilistic program logics

XHL is a Coq library that mechanizes a probabilistic imperative language
(`pwhile`) together with several Hoare-style program logics built on top of it,
and the mathematical backbone (couplings, Strassen's theorem).

## Build instructions

### Dependencies

The library currently requires a forked branch of `math-comp/analysis` that
exposes developments used for `ehl/``:

  <https://github.com/lyonel2017/analysis/tree/feature-esum-psum>


### Building

```sh
make           # dune build
make clean     # dune clean
make install   # dune install
```

## Directory layout

### `pwhile/` — Probabilistic While language and semantics

Defines the syntax of a probabilistic imperative language and its denotational
semantics.

### `hl/` — Hoare logic

Classical (partial-correctness) Hoare logic for the deterministic fragment of
`pwhile`.

### `phl/` — Probabilistic Hoare logic

Extends Hoare logic to probabilistic programs


### `prhl/` — Probabilistic relational Hoare logic

Extends Relational Hoare logic to reasoning about pairs of probabilistic
programs through *couplings*.

*Reference:* Barthe, Grégoire, Zanella-Béguelin — *Formal certification of
code-based cryptographic proofs*, POPL 2009.

### `ehl/` — Expectation Hoare logic

Reasons about *expected values* rather than probabilities.

*References:* Avanzini, Barthe, Grégoire, Moser, Vanoni — *Hopping Proofs of
Expectation-Based Properties: Applications to Skiplists and Security Proofs*,
OOPSLA 2024.

### `erhl/` — Quantitative probabilistic relational Hoare logic

The relational counterpart of `ehl/`: pre- and post-conditions are relational
*expectations*, and validity is witnessed by ★-couplings, so the two programs
need not have the same termination probability.  `erhl_stmt.v` holds the
definitions (★-extension, ★-couplings, the two forms of validity, contracts);
`erhl.v` holds the deductive system.

*Reference:* Avanzini, Barthe, Davoli, Grégoire — *A Quantitative Probabilistic
Relational Hoare Logic*, POPL 2025.

### `ellora/` — Ellora: a distributional Hoare logic

A Hoare logic whose assertions are predicates over distributions.

*Reference:* Barthe, Espitau, Gaboardi, Grégoire, Hsu, Strub — *An
Assertion-Based Program Logic for Probabilistic Programs*, ESOP 2018.

### `strassen/` — Strassen's theorem and coupling theory

Mathematical backbone used by the relational and distributional logics.

*Reference: Barthe, Espitau, Hsu, Sato, Strub
*Relational ⋆-Liftings for Differential Privacy*
