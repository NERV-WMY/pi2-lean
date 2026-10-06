# A 1/π² identity in Lean

A Lean 4 proof of the real-series identity

$$
\sum_{n=0}^{\infty}\frac{(6n)!}{(n!)^6}
\frac{532n^2+126n+9}{10^{6n}}=\frac{375}{4\pi^2}.
$$

The proof includes convergence. Its final theorems are
[`Row12.row12_hasSum`, `Row12.row12_summable`, and `Row12.row12_tsum`](Row12/ScalarEvaluation.lean).
They have no additional hypotheses. Their only axioms are Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

## Build

Install [Lean through elan](https://lean-lang.org/install/) and run:

```sh
lake build Row12
python3 scripts/verify.py
```

The first build retrieves pinned dependencies and may take substantial time.
The pins are Lean **4.33.1** and Mathlib
**db584cd6d46c92f209a44c0f1c829460d327499d**. This repository contains every
Row12 source dependency, including Euler and signed Gauss support.

## Proof

The argument converts the series to a Hadamard integral, constructs an
explicit rational primitive, removes its apparent singularity, and evaluates
the endpoints using a Gauss transformation and a Wronskian identity.

Read the complete [proof PDF](docs/ROW12_PROOF.pdf) or its
[standalone TeX source](docs/ROW12_PROOF.tex). The TeX document also prints an
exact rational certificate checker.

This repository formalizes the displayed scalar identity.

## Verification and credit

Local build and axiom checks passed ([record](verification/STATUS.md)).
Developed with OpenAI Codex assistance, using Lean and Mathlib.

License: [Apache-2.0](LICENSE).
