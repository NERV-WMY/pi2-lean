# Row12 release verification

7 October 2026.

**Claim and scope:** the complete real-series identity displayed in README.md,
including convergence and the unconditional HasSum, Summable and tsum exports.
**Proof status:** Complete. **Open premises:** None in this scalar chain.
**Evidence:** [ARG] the connected formal derivation; [ONE] the recorded build,
source hashes and axiom queries. **Review:** No substantive defect found in the
original connected-proof review of 7 October 2026. The initial release inspection
checked source fidelity and packaging. A subsequent user-requested mathematical
recheck is recorded in [DERIVATION_RECHECK.md](DERIVATION_RECHECK.md); it found no
substantive defect in the derivation and its endpoint normalization.
**Human mathematical acceptance:** Pending.

## Final release check

- All 69 owned Lean files were copied byte for byte from the completed proofs.
- Every owned proof artifact was rebuilt in this assembled package. No original
  Row12, Euler or signed Gauss compiled artifact was copied into it.
- The build passed under Lean 4.33.1 with trust zero and warnings as errors.
  Its complete output is [build.log](build.log).
- The final literal statements and three axiom lists were queried again;
  [final-axioms.txt](final-axioms.txt) records the successful verification script.
  Each final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- The package declares the nine public Git dependencies at recorded revisions.
  The main pin is Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

The local release check used isolated Git checkouts of those revisions and
copies of retained dependency build caches. The shared original checkouts and
caches were unchanged. Only Mathlib's original local toolchain file differed
from its Git revision; the isolated checkout restored the revision's file.
There was no inherited LEAN_PATH or custom FLT/Hodge source dependency.

## Fresh-machine boundary

An internet-only fresh checkout and hosted GitHub CI have not yet been run.
The included workflow builds the package and repeats the final source/axiom
checks. This record claims the successful local release check above.

Mathlib at the pinned revision declares Lean 4.33.0 in its own toolchain file;
this root package deliberately retains the checked Lean 4.33.1. The workflow
does not request the upstream Mathlib cache, which may use that older runtime.
A first build can compile dependencies from source; later CI runs can reuse
GitHub's runtime-specific cache.

For the manuscript's review and status-only update, see
[docs/PROVENANCE.md](../docs/PROVENANCE.md).
