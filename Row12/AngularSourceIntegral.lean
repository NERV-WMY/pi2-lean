import Row12.AngularSourceCertificate
import Row12.AngularContourFrame
import Row12.OuterPrimitive
import Mathlib.Analysis.Calculus.FDeriv.Analytic

#print axioms Row12.angular_source_actual_identity

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

theorem angular_source_polynomial_analyticAt (c : Fin 6 → ℂ) (s : ℂ) :
    AnalyticAt ℂ (angularSourcePolynomial c) s := by
  unfold angularSourcePolynomial
  exact Finset.analyticAt_fun_sum _ (fun k _ =>
    analyticAt_const.mul (analyticAt_id.pow k.val))

theorem angular_source_primitive_entry_analyticAt (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0) (hs0 : s ≠ 0)
    (i j : Fin 3) :
    AnalyticAt ℂ (fun z => angularLiteralPrimitive x z i j) s := by
  change AnalyticAt ℂ (fun z =>
    angularSourcePolynomial (angularPrimitiveCoefficients x i j) z /
      (angularPrimitiveScale x i j * z ^ angularPrimitivePole i j)) s
  exact (angular_source_polynomial_analyticAt _ s).div
    (analyticAt_const.mul (analyticAt_id.pow (angularPrimitivePole i j)))
    (mul_ne_zero (angular_source_scale_ne_zero x hx0 hx25 hx50 i j)
      (pow_ne_zero _ hs0))

theorem angular_source_primitive_pair_analyticAt (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0) (hs0 : s ≠ 0)
    (hs : ‖s‖ < 1) (hb : ‖(angularSourceLambda x)/s‖ < 1) :
    AnalyticAt ℂ (angularSourcePrimitivePair x) s := by
  have hdiv : AnalyticAt ℂ (fun z : ℂ => (angularSourceLambda x)/z) s :=
    analyticAt_const.div analyticAt_id hs0
  have hY (i : Fin 3) : AnalyticAt ℂ (fun z => nativeState z i) s :=
    nativeState_entry_analyticAt i s hs
  have hZ (i : Fin 3) :
      AnalyticAt ℂ (fun z => nativeState ((angularSourceLambda x)/z) i) s :=
    (nativeState_entry_analyticAt i ((angularSourceLambda x)/s) hb).fun_comp hdiv
  unfold angularSourcePrimitivePair angularTensorPair
  exact Finset.analyticAt_fun_sum _ (fun i _ =>
    Finset.analyticAt_fun_sum _ (fun j _ =>
      ((angular_source_primitive_entry_analyticAt x s hx0 hx25 hx50 hs0 i j).mul
        (hY i)).mul (hZ j)))

theorem angular_source_primitive_deriv_circleIntegrable (x : ℂ) {r : ℝ}
    (hx0 : x ≠ 0) (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖angularSourceLambda x‖ < r) :
    CircleIntegrable (deriv (angularSourcePrimitivePair x)) 0 r := by
  have hc : ContinuousOn (deriv (angularSourcePrimitivePair x)) (sphere 0 r) := by
    intro s hs
    obtain ⟨hs0,_,_,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
    exact (angular_source_primitive_pair_analyticAt x s hx0 hx25 hx50 hs0 hsn hbn).deriv.continuousAt.continuousWithinAt
  exact hc.circleIntegrable hr.le

theorem angular_source_primitive_deriv_circleIntegral_zero (x : ℂ) {r : ℝ}
    (hx0 : x ≠ 0) (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖angularSourceLambda x‖ < r) :
    (∮ s in C(0,r), deriv (angularSourcePrimitivePair x) s) = 0 := by
  apply circleIntegral_exactDerivative (angularSourcePrimitivePair x)
    (deriv (angularSourcePrimitivePair x)) hr.le
  intro s hs
  obtain ⟨hs0,_,_,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
  exact (angular_source_primitive_pair_hasDerivAt x s hx0 hx25 hx50 hs0 hsn hbn).differentiableAt.hasDerivAt

theorem angular_source_circleIntegrable (x : ℂ) {r : ℝ}
    (hx0 : x ≠ 0) (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖angularSourceLambda x‖ < r) :
    CircleIntegrable (angularSourceIntegrand x) 0 r := by
  apply (circleIntegrable_congr (by
    intro s hs
    have hsp : s ∈ sphere (0:ℂ) r := by
      simpa only [abs_of_nonneg hr.le] using hs
    obtain ⟨hs0,hs1,hsl,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hsp
    exact angular_source_actual_identity x s hx0 hx25 hx50 hs0 hs1 hsl hsn hbn)).2
  exact (angular_nf_circleIntegrable (angularSourceCoordinates x)
    (angularSourceLambda x) hr hr1 hl).add
    (angular_source_primitive_deriv_circleIntegrable x hx0 hx25 hx50 hr hr1 hl)

noncomputable def angularSourceIntegral (x : ℂ) (r : ℝ) : ℂ :=
  (2*Real.pi*I : ℂ)⁻¹ * ∮ s in C(0,r), angularSourceIntegrand x s

theorem angular_source_integral_eq_actual (x : ℂ) {r : ℝ}
    (hx0 : x ≠ 0) (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖angularSourceLambda x‖ < r) :
    angularSourceIntegral x r =
      dotProduct (angularSourceCoordinates x) (sixthNormalState (angularSourceLambda x)) := by
  have hFi := angular_nf_circleIntegrable (angularSourceCoordinates x)
    (angularSourceLambda x) hr hr1 hl
  have hPi := angular_source_primitive_deriv_circleIntegrable x hx0 hx25 hx50 hr hr1 hl
  have hPzero := angular_source_primitive_deriv_circleIntegral_zero x hx0 hx25 hx50 hr hr1 hl
  have he : (∮ s in C(0,r), angularSourceIntegrand x s) =
      (∮ s in C(0,r), angularNFIntegrand (angularSourceCoordinates x)
        (angularSourceLambda x) s) := by
    calc
      _ = ∮ s in C(0,r), angularNFIntegrand (angularSourceCoordinates x)
          (angularSourceLambda x) s + deriv (angularSourcePrimitivePair x) s := by
        apply circleIntegral.integral_congr hr.le
        intro s hs
        obtain ⟨hs0,hs1,hsl,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
        exact angular_source_actual_identity x s hx0 hx25 hx50 hs0 hs1 hsl hsn hbn
      _ = _ := by rw [circleIntegral.integral_add hFi hPi, hPzero, add_zero]
  unfold angularSourceIntegral
  rw [he]
  exact angular_nf_integral_eq_actual (angularSourceCoordinates x)
    (angularSourceLambda x) (angular_source_lambda_ne_zero x hx0) hr hr1 hl

theorem angular_source_coordinates_eq_outer (x : ℂ) :
    angularSourceCoordinates x = outerSourceRow x := by
  rfl

theorem angular_source_lambda_eq_outer (x : ℂ) :
    angularSourceLambda x = outerPrimitiveLambda x := by
  rfl

theorem angular_source_integral_eq_outer (x : ℂ) {r : ℝ}
    (hx0 : x ≠ 0) (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖outerPrimitiveLambda x‖ < r) :
    angularSourceIntegral x r =
      dotProduct (outerSourceRow x) (sixthNormalState (outerPrimitiveLambda x)) := by
  rw [← angular_source_coordinates_eq_outer, ← angular_source_lambda_eq_outer]
  exact angular_source_integral_eq_actual x hx0 hx25 hx50 hr hr1 hl

end Row12

#print axioms Row12.angular_source_polynomial_analyticAt
#print axioms Row12.angular_source_primitive_entry_analyticAt
#print axioms Row12.angular_source_primitive_pair_analyticAt
#print axioms Row12.angular_source_primitive_deriv_circleIntegrable
#print axioms Row12.angular_source_primitive_deriv_circleIntegral_zero
#print axioms Row12.angular_source_circleIntegrable
#print axioms Row12.angular_source_integral_eq_actual
#print axioms Row12.angular_source_coordinates_eq_outer
#print axioms Row12.angular_source_lambda_eq_outer
#print axioms Row12.angular_source_integral_eq_outer
