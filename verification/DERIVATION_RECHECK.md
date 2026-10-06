# Derivation recheck

7 October 2026. Requested by the user before public release.

**Claim:**

\[
\sum_{n=0}^{\infty}\frac{(6n)!}{(n!)^6}
\frac{532n^2+126n+9}{10^{6n}}=\frac{375}{4\pi^2}.
\]

**Scope:** the literal real series, its convergence, and the complete scalar
dependency chain in [ROW12_PROOF.tex](../docs/ROW12_PROOF.tex) and the connected
Lean exports. Higher Gamma derivatives and other Hodge targets are outside this
review. **Evidence:** [ARG] the mathematical derivation and review; [ONE] the
recorded exact executions. **Proof status:** Complete in this scope.
**Open premises:** None in the checked scalar chain. **Review:** No substantive
defect found. **Human mathematical acceptance:** Pending.

## Checks of the connected argument

The coordinator read the series-to-integral reduction, rational construction,
contour argument, apparent-singularity removal, upper endpoint and final
integration. A fresh GPT-6.1-Sol reviewer with Ultra reasoning independently
checked the signed Gauss transformation, Euler normalization, Wronskian and
lower-endpoint residue. This was a read-only check of the existing proof.

1. **Convergence and integral reduction.** The multinomial bound gives a
   summable polynomial times geometric majorant with
   `rho = 729/15625 = 6^6/10^6`. The native coefficient recurrence and the
   moment recurrence give
   `(6n+1) a_n^2 I_(3n) = (6n)!/(6^(6n) (n!)^6)`.
   The loaded polynomial is exactly
   `Q(n) = (1+6n)(9+126n+532n^2)`.
   Uniform majorants justify termwise integration, including the constant
   term. This preserves the literal factorial series and its normalization.

2. **Rational identity.** The dual-state connection, covariant derivative
   signs, tensor ordering and angular primitive were checked against the
   displayed source. The checker constructs that source from the complete
   beta formulas. It verifies all nine zero remainders in division by `f^2`,
   the rational reduction and factorization, the six-state connection and
   anchor rows, and the outer primitive with all 90 printed coefficients.
   Its identities use exact rational arithmetic, not numerical fitting.
   The resulting balanced primitive satisfies
   `E'(U) = -Q(theta_lambda) h(lambda) / 3375`.

3. **Contours and the interior singularity.** For `0 < U < 1`, the balanced
   circle keeps both native arguments inside their convergence disks. The
   signed root formulas put exactly the specified pole inside the circle.
   At `x = 50/99`, the apparent singularity has a finite meromorphic order
   while the derivative has a finite limit. A negative Laurent term would
   contradict this derivative bound. Removal therefore gives one common
   two-sided limit, as required when the integral is split at that point.

4. **Upper endpoint.** The three dual-state components are of order `q^2`.
   Together with the contour denominator bounds this makes the beta term
   tend to zero. The printed primitive coefficients cancel the possible
   divergent and constant terms in the outer contribution. The remainder
   estimates then give `E(1-) = 0`. These cancellations were also checked
   exactly by the small-identity script.

5. **Gauss transformation and lower endpoint.** The fresh reviewer checked
   the signed discriminants, pullback derivatives, gauge equations,
   normalization at zero and continuation through the sign change. The
   Euler beta integral independently fixes the logarithmic endpoint
   coefficient. The differentiated integral and logarithmic bounds give
   the stated Wronskian normalization. Consequently the actual native value
   is `3 F(27/125) + 28 theta F(27/125) = 5 sqrt(5)/pi`.
   The positively oriented annulus contributes the full residue. The
   resulting quadratic expression is
   `beta(0+) = (3 F + 28 theta F)^2 / 4500 = 1/(36 pi^2)`.
   The outer contribution tends to zero at this endpoint.

6. **Final evaluation.** Convergence, the common interior limit and the
   endpoint limits justify the fundamental theorem of calculus on the two
   intervals. Thus the original series equals
   `3375 (E(0+) - E(1-)) = 3375/(36 pi^2) = 375/(4 pi^2)`.
   The connected Lean statements assert the literal HasSum, Summable and
   tsum results with no additional hypotheses. Their previously recorded
   fresh release build and standard axiom lists remain applicable because
   no Lean source was changed.

## Fresh exact executions

Both public manuscript checkers were rerun successfully with the installed
SymPy 1.14.0. The rational certificate run reported 62.071 seconds. Their
stdout is retained in [derivation-checks.txt](derivation-checks.txt).

- `docs/CERTIFICATE_TRANSCRIPTION_CHECK.py`: all nine source entries have
  zero division remainder; the angular primitive and all finite printed
  rational-function identities pass.
- `docs/DOCUMENT_SMALL_CHECKS.py`: all small manuscript identities and
  endpoint cancellations pass.

The symbolic executions check the finite algebraic components. The analytic
steps above were inspected as mathematical arguments; a successful script is
not their justification. No mathematical correction was identified. The
manuscript and all 69 Lean source files retain their checked bytes. This
additional review does not promote evidence labels or supply human acceptance.
