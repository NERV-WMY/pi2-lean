# Manuscript provenance

The proof document and its two review records are unchanged copies of the
completed scalar manuscript package of 7 October 2026.

- The mathematically reviewed TeX source has SHA-256
  `B47D9842D079F347BDE913DC10601B84DC6A510158EC9D09A67485A6EDBC93C4`.
- The released TeX source has SHA-256
  `DBD38D54D25882977A1B1A07A88F0C7FD98EB2E10127E23659A7714C8B90EC01`.
- The released PDF has SHA-256
  `8F6CFE4FE4A310F52329C6756D9C244B5044CFEAF5D02EEBB70A13A962234EFA`.

The two TeX versions differ only in the opening and closing status notes,
which were updated after Lean verification finished. The mathematical text,
coefficients and embedded certificate checker are identical. The affected
status update is explained in VERIFICATION_RECORD.md; DOCUMENT_REVIEW.md
records the mathematical review and its checked amendments.

Historical paths in those records refer to the retained original project.
The TeX source is standalone and prints every rational certificate input.
The accompanying Python certificate checks use SymPy. These optional checks
are separate from the Lean build, whose dependency pins and fresh release
verification are recorded in ../verification/STATUS.md.

To run the optional manuscript checks:

```sh
python3 -m pip install -r docs/requirements.txt
python3 docs/CERTIFICATE_TRANSCRIPTION_CHECK.py
python3 docs/DOCUMENT_SMALL_CHECKS.py
```
