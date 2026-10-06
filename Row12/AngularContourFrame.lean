import Row12.AngularContour

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

theorem angular_nf_integral_linear (v : Fin 6 → ℂ) (lambda : ℂ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖lambda‖ < r) :
    angularNFIntegral v lambda r = dotProduct v (angularContourState lambda r) := by
  have he (s : ℂ) : angularNFIntegrand v lambda s =
      ∑ i : Fin 6, v i*angularNFIntegrand (Pi.single i 1) lambda s := by
    simp only [angular_nf_integrand_linear, single_dotProduct, one_mul]
    rfl
  have hi (i : Fin 6) : CircleIntegrable
      (fun s => v i*angularNFIntegrand (Pi.single i 1) lambda s) 0 r :=
    (angular_nf_circleIntegrable (Pi.single i 1) lambda hr hr1 hl).const_mul (v i)
  unfold angularNFIntegral
  simp_rw [he]
  rw [circleIntegral.integral_fun_sum (fun i _ => hi i), Finset.mul_sum]
  simp only [dotProduct, angularContourState, angularNFIntegral,
    circleIntegral.integral_const_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem angular_nf_integral_cyclic (n : ℕ) (hn : n < 6) (lambda : ℂ) {r : ℝ}
    (hl0 : lambda ≠ 0) (hr : 0 < r) (hr1 : r < 1) (hl : ‖lambda‖ < r) :
    angularNFIntegral (sixthCyclicMatrix ⟨n,hn⟩) lambda r =
      squaredNativeEuler n lambda := by
  induction n generalizing lambda with
  | zero => exact angular_nf_integral_anchor lambda hl0 hr hr1 hl
  | succ n ih =>
    have hn5 : n < 5 := by omega
    have hn6 : n < 6 := by omega
    let j : Fin 5 := ⟨n,hn5⟩
    have hl1 : lambda ≠ 1 := by intro he; simp [he] at hl; linarith
    have hd := angular_nf_integral_hasDerivAt
      (sixthCyclicMatrix j.castSucc) lambda hl0 hr hr1 hl
    rw [angular_cyclic_row_action j lambda hl1] at hd
    have he : (fun z => angularNFIntegral (sixthCyclicMatrix j.castSucc) z r) =ᶠ[nhds lambda]
        squaredNativeEuler n := by
      filter_upwards [eventually_ne_nhds hl0,
        continuous_norm.continuousAt.tendsto.eventually (Iio_mem_nhds hl)] with z hz0 hz
      exact ih hn6 z hz0 hz
    have hder : deriv (fun z => angularNFIntegral (sixthCyclicMatrix j.castSucc) z r) lambda =
        deriv (squaredNativeEuler n) lambda := he.deriv_eq
    have ha : angularNFIntegral (sixthCyclicMatrix j.succ) lambda r =
        lambda*deriv (squaredNativeEuler n) lambda := by
      rw [← hder,hd.deriv]
      field_simp [hl0]
    have hj : j.succ = (⟨n+1,hn⟩ : Fin 6) := by apply Fin.ext; rfl
    rw [hj] at ha
    exact ha.trans (squaredNativeEuler_succ_eq n lambda (hl.trans hr1)).symm

theorem angular_contour_cyclic_frame (lambda : ℂ) {r : ℝ}
    (hl0 : lambda ≠ 0) (hr : 0 < r) (hr1 : r < 1) (hl : ‖lambda‖ < r) :
    sixthCyclicMatrix.mulVec (angularContourState lambda r) = sixthState lambda := by
  ext i
  change dotProduct (sixthCyclicMatrix i) (angularContourState lambda r) = _
  rw [← angular_nf_integral_linear _ lambda hr hr1 hl]
  have hh := angular_nf_integral_cyclic i.val i.isLt lambda hl0 hr hr1 hl
  fin_cases i <;> simpa [sixthState] using hh

theorem angular_contour_state_eq_actual (lambda : ℂ) {r : ℝ}
    (hl0 : lambda ≠ 0) (hr : 0 < r) (hr1 : r < 1) (hl : ‖lambda‖ < r) :
    angularContourState lambda r = sixthNormalState lambda := by
  have hh := congrArg (sixthCyclicInverse.mulVec)
    (angular_contour_cyclic_frame lambda hl0 hr hr1 hl)
  rw [Matrix.mulVec_mulVec, sixth_cyclic_inverse_left, Matrix.one_mulVec] at hh
  exact hh

theorem angular_nf_integral_eq_actual (v : Fin 6 → ℂ) (lambda : ℂ) {r : ℝ}
    (hl0 : lambda ≠ 0) (hr : 0 < r) (hr1 : r < 1) (hl : ‖lambda‖ < r) :
    angularNFIntegral v lambda r = dotProduct v (sixthNormalState lambda) := by
  rw [angular_nf_integral_linear v lambda hr hr1 hl,
    angular_contour_state_eq_actual lambda hl0 hr hr1 hl]

end Row12

#print axioms Row12.angular_nf_integral_linear
#print axioms Row12.angular_nf_integral_cyclic
#print axioms Row12.angular_contour_cyclic_frame
#print axioms Row12.angular_contour_state_eq_actual
#print axioms Row12.angular_nf_integral_eq_actual
