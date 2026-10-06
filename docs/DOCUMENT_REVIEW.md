# Document-level mathematical review of the scalar Row12 manuscript

7 October 2026. One fresh reviewer, `row12_tex_manuscript_review`, GPT-6.1-Sol / Ultra.
Owned artifact: this report only. The manuscript, frozen proofs, coefficients,
and formalization were read only. This is a review of the assembled scalar
manuscript and its transcription; it does not repeat the original Row12
audit or take over the connected Lean work.

Initial fully reviewed source:
`ROW12_PROOF.tex`, SHA-256
`EDD5A7E60B57EA9227466F24640BD2DA75E53776AE705CF7A30629719E56CB1C`.

The first source read had SHA-256
`76F2F466AD04352E64370018628480702C43CFB3FD07A0BE248751DFC4F67A4B`.
During review the author corrected the covariant-derivative macro, separated
the source polynomial names from the witness rows, removed a duplicated word,
and adjusted display layout. The resulting formulas and affected text were
read again at the reviewed hash above.

**Verdict: No substantive defect found.** The manuscript supplies a complete
human-checkable analytic derivation of the literal zeroth scalar, with its
finite rational computation explicitly delimited in Appendix A. The two small
annotation clarifications below were applied and checked in the affected-cone
addendum. They do not change a formula, mathematical dependency, or verdict.

## Exact claim and status

**Claim:** the absolutely convergent literal series satisfies

\[
 \sum_{n=0}^{\infty}\frac{(6n)!}{(n!)^6}
 \frac{532n^2+126n+9}{10^{6n}}=\frac{375}{4\pi^2}.
\]

**Scope:** the stated zeroth scalar with
\(\rho=729/15625,\ u=27/125\), the positive angular circles, the full printed
coefficient one-form, all ninety outer coefficients, the signed real Gauss
transformation on \(h>8\), and the displayed endpoint normalizations.
No Gamma jet, original CY4 marked-class comparison, weighted \(p^5\) result,
or full C5 completion is included.

**Evidence:** [ARG] the analytic derivation, finite elimination argument, and
this mathematical review; [ONE] the retained exact rational identities and
author's document checks. The coefficient transcription comparison performed
in this review found all ninety entries literally identical to the frozen
s14 table. No independent mathematical implementation, [VER] promotion, or
literature adoption is claimed.

**Proof status:** Complete for the human-checkable scalar theorem with the
supplied finite rational certificate.

**Open premises:** None in this mathematical scope. Execution of the new
standalone listing is an author-owned verification task; its successful final
result is recorded in the closure below, separately from the read-only review.
The connected Lean
value theorem remains Incomplete and is outside this verdict.

**Review:** No substantive defect found, 7 October 2026, this report, for the
source hash above and the exact dependency boundary below.

**Human acceptance:** Pending.

## What was actually checked

Every load-bearing proof paragraph and the entire exact listing in
`ROW12_PROOF.tex` were read. The relevant originals were read in
`SCALAR_INTEGRAL_ROUTE.md`, `SCALAR_ROUTE_REVIEW.md`,
`row12_strict_audit_2026-10-06/READABLE_PROOF.md` and its `REVIEW.md`.
The frozen s08 proof and s03, s10, and s14 rational inputs were followed for
the source matrices, cyclic matrix, outer basis order, and literal witness
coefficients. Prior review verdicts were context, not substitutes for checking
the assembled argument. Original geometric class maps and Gamma jets are not
premises of this scalar compression.

No original certificate was replayed, no solver or Lean process was run,
and no new review round was dispatched. The author's completed small
checks were not repeated. A direct source comparison established that the
printed listing equals `CERTIFICATE_TRANSCRIPTION_CHECK.py` after removal
of terminal whitespace; that script's SHA-256 was
`BF56ABD1F50064DF978198409284D975AED53891FC32AD5D221C23CD222AF7A6`.

The reviewed proof closes the following dependencies.

1. **Literal series, moments, and Hadamard identity.** The native factorial
   coefficient has the stated successive ratio and constant term. The
   integration-by-parts recurrence for \(I_m\) gives exactly
   \((6n+1)a_n^2I_{3n}=(6n)!/(6^{6n}(n!)^6)\). Therefore the radial load is
   \(Q=(1+6z)P\), with coefficients \(9,180,1288,3192\).
   The multinomial bound proves absolute convergence independently of the
   value. The geometric majorants justify the radial interchange, angular
   coefficient extraction, and local parameter differentiation, including
   the \(n=0\) convention. The final argument evaluates the entire loaded
   integral, rather than replacing it by its contact value.

2. **Dual frame, complete beta, and source sign.** \(W=T^{\mathsf T}Y\)
   satisfies \(W'=-\mathsf A^{\mathsf T}W\); consequently the signs and
   transpose placements in both coefficient derivatives are correct.
   With \(B_s=UT_s\), \(x_U=-2U\), and \(b_U=-6Ub/x\), the appendix's
   \(\mathsf K\) is precisely
   \(-\mathcal D_U B_s+\mathcal D_sB_U\).
   Both beta components and the second term of \(B_s\) are present.
   Its contour derivative is \(-G\mathbf v\). No metric scale, free period
   ratio, physical intersection value, or extra Tate factor is inserted in
   this scalar normalization.

3. **Finite angular and outer identities.** Row-by-row flattening and the
   plus angular connection agree with the native product column.
   The anchor primitive, all six parameter-action primitives, and the
   constant cyclic matrix give the actual analytic state identities.
   Covariant angular exact terms integrate to zero because their pairings
   are single-valued on the circle; regularity inside the circle is not
   required. The elimination blocks have the stated nonintegral spectra,
   so higher poles and polynomial terms are removed in finitely many steps.
   In the uniqueness argument a possible remaining constant primitive is
   killed by invertible \(R_0\).
   The ninety entries and fifteen basis functions are fully specified.
   Converting the complete outer identity with
   \(\mathcal V=U\mathbf v\) gives the displayed derivative of
   \(U\xi\mathbf v\), with the factor \(3375\) and signs correct.
   Combining it with the beta derivative gives
   \(\mathcal E'=-Q(\theta_\lambda)h/3375\).

4. **Escape and upper endpoint.** At the escape fiber the roots are
   \(\lambda_e\) and \(1\). A fixed intermediate circle yields a genuinely
   meromorphic continuation of the combined \(\mathcal E\). Its holomorphic
   derivative rules out every negative Laurent coefficient, so the two
   real limits agree; no term of either coefficient is discarded.
   Near \(U=1\), \(W(q)=O(q^2)\) uniformly in a disk and
   \(|f|\geq 2r(m-r)\geq c xr\). Including the circle length gives
   \(\mathfrak b=O(x^2)\).
   The Laurent cancellations include both escape contributions to
   \(\xi_0\). The state remainder is \(O(x^6)\), so after multiplication by
   \(\xi=O(x^{-4})\) it contributes \(O(x^2)\).
   Hence the complete upper limit is zero.

5. **Lower endpoint and full positive residue.** The fixed inner circle
   can be chosen with \(\rho<r_0<u\), and both native arguments stay in
   compact unit subdisks. Its beta integral tends to zero. The annulus to
   the balanced circle contains only \(\sigma_+\), so positive orientation
   and \(2\pi i/\tau=1\) give a full positive residue.
   Direct division by \(f'(\sigma_+)\) gives
   \((UL_P+\sqrt M R_P)/d\), whose limit is \(4R_P(1)/d(1)\).
   The displayed endpoint matrix and native Gauss equation produce
   \(\{3F(u)+28\theta F(u)\}^2/4500\), with the stated coefficients.

6. **Actual signed transformation, normalization, and contact.** The
   pullback uses the signed \(h-512\) throughout. The explicit \(z\)
   derivatives, pullback coefficients, logarithmic gauge derivatives,
   and ordinary \(h\) equations are consistent.
   Both compared solutions are analytic at \(z=0\), have value one,
   and satisfy the same equation with \(B_2(0)=C_2(0)=0\).
   The first-nonzero-coefficient argument establishes normalized analytic
   uniqueness there. The ordinary \(h\) equation is nonsingular on
   \(h>8\), including \(h=512\); \(p_2(512)=1/2\) presents no branch switch.
   Thus the actual transformation and its ordinary derivative are proved
   on the needed open interval.
   The symmetric-square identity gives \(F=g^2\) by its coefficient
   recurrence and analytic continuation.
   The elementary beta residue evaluation gives \(B(5/6,1/6)=2\pi\).
   Differentiation of the actual Euler integral and the displayed
   integrable majorant prove
   \(\delta H'(1-\delta)\to1/(2\pi)\).
   The independent \(H(1-\delta)\leq\delta^{-1/6}\) bound kills the other
   Wronskian term. This fixes its sign and absolute normalization.
   At \(h=64\) the signed complementary branch and all three moving
   logarithmic derivatives give the stated theta relation and
   \(3F(u)+28\theta F(u)=5\sqrt5/\pi\).

7. **Completion.** The lower outer correction vanishes since \(\xi\) is
   finite at \(x=1\). The lower beta residue is therefore
   \(1/(36\pi^2)\). The loaded radial integrand extends continuously and
   boundedly to \([0,1]\). Applying FTC to closed interior intervals,
   after escape removability, and then taking both endpoint limits
   gives \(3375/(36\pi^2)=375/(4\pi^2)\).

## Exact finite computation boundary

The nine-entry angular primitive and six source coordinates are defined by
the terminating elimination in the printed listing; they are not each
expanded as separate long rational formulas. The listing constructs and
retains `eta`, checks the full source identity and both residue
factorizations, and then tests all six outer identities using the fixed
ninety-entry witness. The coefficient-field scale is independent of \(s\)
and is explicitly undone, so it does not alter an angular derivative.
This is an explicit finite exact-arithmetic certificate, with a reproducible
definition of its witness. It is not a claim based on rank, an unknown
primitive, a fitted source row, or numerical tolerance.

The analytic contour, escape, and endpoint arguments remain separate
human-checkable [ARG] steps. A successful execution of the listing tests
the stated rational identities; it does not on its own certify those
analytic steps or provide formal Lean verification.

## Nonblocking annotation clarifications

1. The listing comment currently says
   `beta/tau = T_U dU + U*T_s ds`. The manuscript itself defines
   the already normalized \(\beta_N=T_U\,dU+UT_s\,ds\), and it introduces
   no separate unnormalized `beta` in this appendix. Replace that
   comment with `beta_N = T_U dU + U*T_s ds` to make the listing's
   normalization agree literally with its surrounding definition.
   The implemented matrices and contour normalization are correct.

2. The definition of \(\mathbf v(\lambda)\) prints \(\lambda<r<1\)
   and then asserts holomorphy in the punctured complex unit disk.
   For that complex extension, state \(|\lambda|<r<1\), while retaining
   \(0<\lambda<1\) for the actual real radial contour.
   The existing fixed-circle proof already supplies this extension;
   only its notation needs the modulus.

Neither clarification requires repeating the full proof or the original
audit. Any mathematical change to a formula must return to this same
reviewer for its affected dependency cone. Final version/status and layout
changes should retain a new exact source hash beside the preserved hash
above; this review makes no PDF-layout or completed-Lean claim.


## Affected-cone check of the replacement polynomial-source recipe

The same reviewer checked the replacement recipe and the two annotation
clarifications, without repeating the unchanged analytic audit.

**Final reviewed TeX SHA-256:**
`6F654621D797ED1611288BAEC68A82927A3EB342293D71E43D2C6091E7B7DC26`.

**Replacement checker SHA-256:**
`E6AEB133266C5DA837CF19077A25BF2AF0EB1F8583488623D8A25940C3E53071`.

The complete printed listing is literally identical to that checker after
removal of terminal whitespace. The beta normalization comment now says
`beta_N`, and the six-state definition explicitly requires
\(|\lambda|<r<1\) for the complex extension. Both prior annotations are
resolved. The source form wording, review-status paragraph, and separated
\(J_C/T\) displays introduce no mathematical change.

**Affected-cone verdict: No substantive defect found.** The replacement
computes exactly the same \(\mathsf K\) and scaled flattened source as
the previously reviewed rational recipe. It changes the order of exact
algebraic operations, without omitting a coefficient or assuming that a
source pole cancels.

Here is the explicit equivalence. Let \(t_{ij}\) and \(u_{ij}\) be the
printed numerator matrices, so the actual appendix coefficients are
\(T_s=t/(Df)\) and \(T_U=u/(Df)\); let \(r=1-x\).
The replacement matrices satisfy

\[
 \texttt{asbar}=s(1-s)\mathsf A(s),\qquad
 \texttt{cbbar}=s(s-\lambda)\,b\mathsf A(b),\qquad b=\lambda/s.
\]

These identities hold entry by entry. In particular the second matrix
contains \(b\mathsf A(b)\), rather than \(\mathsf A(b)\); its first
off-diagonal numerator is \(\lambda(s-\lambda)\).
Its right multiplication in the code uses `cbbar[j][k]`,
which supplies exactly the required transpose.

With \(\delta_s=s^2(1-s)(s-\lambda)\), the ordinary derivative part of
\(D\mathsf K\), written over \(f^2\), has numerator

\[
 A_{ij}=-t_{ij}f+
 2r\{(\partial_xt_{ij})f-t_{ij}f_x-(D'/D)t_{ij}f\}
 +(\partial_su_{ij})f-u_{ij}f_s.
\]

This is precisely `scalar_part`. The \(-t_{ij}\) term comes
from differentiating the explicit \(U\) in \(B_s=UT_s\), the derivative
of \(D\) appears with its minus sign, and both \(f_x\) and \(f_s\)
remain present. Clearing the connection denominator gives the full numerator

\[
\begin{aligned}
 \delta_s A_{ij}
 &-s(s-\lambda)(\texttt{asbar}\,u)_{ij}f\\
 &+(1-s)(u\,\texttt{cbbar}^{\mathsf T})_{ij}f
 -\frac{6r}{x}s(1-s)(t\,\texttt{cbbar}^{\mathsf T})_{ij}f .
\end{aligned}
\]

After division by \(\delta_s f^2\), these last three terms are respectively
\(-\mathsf A(s)u/f\), \(+(b/s)u\mathsf A(b)^{\mathsf T}/f\), and
\(-6rb\,t\mathsf A(b)^{\mathsf T}/(xf)\).
Thus every term of the displayed covariant formula is accounted for.

The replacement divides each numerator by \(f^2\) as polynomials over
\(\mathbb Q(x)\), asserting a zero remainder for all nine entries.
It then multiplies by

\[
 \frac{\texttt{scale}}D
 =\frac{x^5(9x-25)(99x-50)^3}
        {x^4(25-9x)(99x-50)^2}
 =-x(99x-50),
\]

and divides by \(\delta_s\). Hence `alpha` is exactly
`scale` times \(\mathsf K\). The subsequent \(T(s)\) and
\(T(b)^{\mathsf T}\) multiplication, nine-entry flattening, plus angular
connection, retained primitive, residue factorization, division by
`scale`, ninety-entry witness, and six outer assertions are
unchanged. The polynomial numerator assertion includes constant rational
denominators and normalizes their leading coefficients exactly; it does
not assume every constant denominator is one.

At this addendum the owner reported that all nine zero-remainder divisions
and the source-transcription boundary had passed. The full normal-form,
primitive, and outer-witness execution was still running. This addendum
therefore records **no full-run execution pass**. The owner is to retain
the actual final result in `VERIFICATION_RECORD.md`.
The formula-equivalence verdict above does not depend on a numerical
residual, an old replay, or concurrent checker execution. The mathematical
claim/status block remains unchanged, evidence remains [ARG]/[ONE], and
human acceptance remains Pending.

## Final affected-cone closure

**Final reviewed manuscript SHA-256:**
`B47D9842D079F347BDE913DC10601B84DC6A510158EC9D09A67485A6EDBC93C4`.

**Final embedded checker SHA-256:**
`C88D0977AAB6C09C4D6C6F364AFE605AEE6F75A1D08BF521BAD2A79E33763EC8`.

The same reviewer checked the final comparison repair and confirmed that the
printed listing equals the final checker after removal of terminal whitespace.
The source polynomial calculation is the one analyzed above. The repair
replaces representation equality of rational field elements by zero tests of
their exact differences. For these `FracElement` values, truth is determined
by the polynomial numerator; the owner inspected the installed implementation
of `__bool__`, which returns `bool(f.numer)`. Thus `not (a-b)` tests the exact
identity (a=b), independent of nonzero denominator units. No tolerance or
sampled evaluation is involved.

The final assertions cover all nine normal-form entries, all nine complete
source/primitive entries, both nine-entry residue factorizations, the full
fixed ninety-coefficient witness, and all six exact outer identities. The
outer residuals still use exact SymPy rational cancellation. These comparisons
are mathematically adequate and preserve the original statement.

The owner reported exit code zero for the single successful final run.
The reviewer read `CERTIFICATE_TRANSCRIPTION_CHECK.output.txt`, which records
all nine zero-remainder (f^2) divisions, the full angular source/primitive
identity, and completion of all finite printed identities in **95.374 seconds**.
This closes the execution-pending status recorded at the preceding boundary.
The detailed owner evidence/build record belongs in `VERIFICATION_RECORD.md`.
The reviewer did not rerun the checker, original certificates, or unchanged
analytic audit.

**Final verdict: No substantive defect found**, for the final manuscript hash
above and the complete scalar scope in the claim block. Both annotations are
resolved. Evidence remains [ARG]/[ONE]; proof status remains Complete for this
human-checkable scalar theorem; open mathematical premises are None; human
mathematical acceptance remains Pending. Connected Lean completion and PDF
layout verification are separate obligations.
