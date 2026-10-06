# Scalar Row12 manuscript verification

7 October 2026. Coordinator-owned final delivery record.

**Claim:** the literal absolutely convergent weighted factorial series in
Theorem 1.1 of ROW12_PROOF.tex equals 375/(4*pi^2).
**Scope:** that scalar equality, its complete radial/angular bridge,
rational antiderivative, interior removability, both endpoint limits, and
independently normalized native Gauss value. Gamma jets, original CY4
marked-class comparisons, weighted p^5 and full C5 are outside this document.
**Evidence:** [ARG] the analytic derivation and finite elimination argument;
[ONE] the fresh exact document checks recorded below. No [VER] promotion.
**Proof status:** Complete for the stated human-checkable scalar theorem.
**Open premises:** None within that mathematical scope.
**Review:** No substantive defect found in the fresh manuscript review and
the same reviewer's affected computational-cone check; DOCUMENT_REVIEW.md.
**Human acceptance:** Pending. Connected scalar Lean verification is Complete;
the completion evidence and subsequent status-only edit are recorded below.

## Frozen deliverables

- ROW12_PROOF.tex: SHA-256
  DBD38D54D25882977A1B1A07A88F0C7FD98EB2E10127E23659A7714C8B90EC01.
- output/pdf/ROW12_PROOF.pdf: 21 pages, SHA-256
  8F6CFE4FE4A310F52329C6756D9C244B5044CFEAF5D02EEBB70A13A962234EFA.
- The single source file includes every coefficient and the entire verifier;
  no external TeX input, certificate file or bibliography is required to compile.

## Actual exact checks

CERTIFICATE_TRANSCRIPTION_CHECK.py, SHA-256
C88D0977AAB6C09C4D6C6F364AFE605AEE6F75A1D08BF521BAD2A79E33763EC8,
completed with exit code zero in 95.374 seconds. Its exact console output
is CERTIFICATE_TRANSCRIPTION_CHECK.output.txt:

    All nine source entries pass exact zero-remainder f^2 division.
    Source transcribed from the complete beta formulas.
    Angular source identity established with its rational primitive.
    All finite printed identities hold over the rational function fields.
    Elapsed seconds: 95.374

This run checked the actual source differential, all nine source entries,
the complete angular primitive identity and parabolic residue factorizations,
and all six outer identities with the literal ninety-coefficient witness.
It read no old result or solver, fitted no source row, and used exact
polynomial/rational arithmetic. The embedded listing matches this executable.
The angular primitive is the program's eta/scale, as explained in the text.

DOCUMENT_SMALL_CHECKS.py, SHA-256
6992E68A1C9BC16F42E6D5790999BE9DFE2EDE6EFE0CDDD9DDDB6F5AB967A2DA,
also finished with exit code zero. It checked the displayed dual-frame
identity, discriminant and escape substitution, endpoint residue matrix and
perfect-square conversion, cyclic endpoint vectors, complete Laurent
cancellations, and printed Gauss gauge identities. Its finite moment controls
supplement the general integration-by-parts proof.

The reviewer compared all ninety entries with the frozen s14 input. Review
and successful arithmetic execution have distinct scopes: neither supplies
formal Lean verification or human mathematical acceptance.

## Compilation and visual inspection

The built-in compiler was unavailable and returned the infrastructure
message "Unable to find standard directories for platform". The source was
opened in the built-in editor, and the existing TeX Live 2026 installation
was used as a fallback; no installation or dependency change occurred.

The final two pdflatex passes succeeded with exit code zero. The final log
has no undefined references, errors, overfull boxes or underfull boxes.
output/pdf/compile-pass8.txt and output/pdf/ROW12_PROOF.log retain the
final build result.

All 21 pages were rendered with installed Poppler and visually inspected.
After the final listing update, unchanged pages were compared pixel for pixel,
and the changed pages were inspected again. No clipped equations, overlapping
text, missing glyphs or broken references were found. Rendering does not
replace the mathematical review.

The slow interrupted arithmetic attempts and implementation repairs are
retained in CERTIFICATE_NOTES.md; they supply no completed source result.
Only the finished exact run above is counted as the new full certificate check.

## Later Lean completion receipt and status-only document update

The user subsequently asked whether the stopped Row12 chats meant that the
formalization was complete. A bounded read-only check confirmed the new final
handoff: the exact literal HasSum, Summable and tsum declarations are
unconditional, and all five verification checks passed. The coordinator read
the elaborated final statements and all three axiom outputs, the successful
package-build tail, the fresh connected-implementation review and goal record.
The source hashes matched the owner's frozen values. A separate bounded
statement-fidelity check found no discrepancy; it performed no build or
mathematical re-audit.

The final implementation is in
C5/row12_lean_2026-10-06/Row12/ScalarEvaluation.lean. Its SHA-256 is
588C8CA8C54F5A8A8D4200D8F024CD7B84937BA6D4E076814325BD5AA77A729E.
The declarations are Row12.row12_hasSum, Row12.row12_summable and
Row12.row12_tsum. Their axiom lists contain exactly propext, Classical.choice
and Quot.sound. Final_statement_axioms.txt, the empty
Final_forbidden_source.txt, Package_build.txt and FINAL_SCALAR_REVIEW.md
retain the corresponding evidence. The goal completion and idle chat status
were also observed. No Lean process was restarted.

Only the opening status note and the final provenance/status paragraph in
this manuscript were changed to record that completion. No definition,
coefficient, proof step or checker changed. The reviewed mathematical source
is preserved as history/ROW12_PROOF_BEFORE_LEAN_STATUS.tex, SHA-256
B47D9842D079F347BDE913DC10601B84DC6A510158EC9D09A67485A6EDBC93C4,
matching DOCUMENT_REVIEW.md. The updated deliverable hashes are listed above.
The PDF was rebuilt successfully; the two changed pages were rendered and
visually checked, with no layout defect. The final log has no warnings.

Formal completion covers only the literal scalar equality and its convergence.
Higher jets, original geometric comparison, weighted p^5 and full C5 remain
outside that Lean goal. Evidence tags and human acceptance remain unchanged.
