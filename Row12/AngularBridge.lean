import Row12.ScalarSeriesIntegral
import Row12.Hadamard

open Set Metric Complex

namespace Row12

theorem angularWeight_eq_cubic (n : ℕ) :
    angularWeight n = 3192 * (n : ℝ) ^ 3 + 1288 * (n : ℝ) ^ 2 + 180 * (n : ℝ) + 9 := by
  unfold angularWeight weight
  ring

theorem coefficient3_sq_le_one (n : ℕ) : coefficient3 n ^ 2 ≤ 1 :=
  pow_le_one₀ (coefficient3_nonneg n) (coefficient3_le_one n)

noncomputable def squaredNativeEuler (k : ℕ) (q : ℂ) : ℂ :=
  ∑' n : ℕ, (coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ k * q ^ n

theorem squaredNativeEuler_summable (k : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => (coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ k * q ^ n) := by
  have hr : ‖‖q‖‖ < 1 := by simpa only [Real.norm_eq_abs, abs_norm] using hq
  apply (summable_pow_mul_geometric_of_norm_lt_one k hr).of_norm_bounded
  intro n
  simp only [norm_mul, norm_pow, Complex.norm_of_nonneg (coefficient3_nonneg n),
    RCLike.norm_natCast]
  calc
    coefficient3 n ^ 2 * (n : ℝ) ^ k * ‖q‖ ^ n ≤ 1 * (n : ℝ) ^ k * ‖q‖ ^ n := by
      gcongr
      exact coefficient3_sq_le_one n
    _ = (n : ℝ) ^ k * ‖q‖ ^ n := by ring

theorem squaredNativeTerm_hasDerivAt (k n : ℕ) (q : ℂ) :
    HasDerivAt (fun q : ℂ => (coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ k * q ^ n)
      ((coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ (k + 1) * q ^ (n - 1)) q := by
  have hd := ((hasDerivAt_id q).pow n).const_mul ((coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ k)
  apply hd.congr_deriv
  simp only [id_eq]
  rw [pow_succ]
  ring

theorem squaredNativeDerivative_bound (k n : ℕ) {r : ℝ}
    (hr : 0 < r) (q : ℂ) (hq : ‖q‖ ≤ r) :
    ‖(coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ (k + 1) * q ^ (n - 1)‖ ≤
      r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n) := by
  simp only [norm_mul, norm_pow, Complex.norm_of_nonneg (coefficient3_nonneg n),
    RCLike.norm_natCast]
  calc
    coefficient3 n ^ 2 * (n : ℝ) ^ (k + 1) * ‖q‖ ^ (n - 1) ≤
        1 * (n : ℝ) ^ (k + 1) * r ^ (n - 1) := by
      gcongr
      exact coefficient3_sq_le_one n
    _ = r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n) := by
      cases n with
      | zero => simp
      | succ n =>
        simp only [Nat.add_sub_cancel, pow_succ]
        field_simp

theorem squaredNativeEuler_hasDerivAt (k : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    HasDerivAt (squaredNativeEuler k)
      (∑' n : ℕ, (coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ (k + 1) * q ^ (n - 1)) q := by
  let r : ℝ := (‖q‖ + 1) / 2
  have hr : 0 < r := by dsimp [r]; nlinarith [norm_nonneg q]
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hqr : ‖q‖ < r := by dsimp [r]; linarith
  have hgeom : Summable (fun n : ℕ => r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (k + 1)
      (by simpa only [Real.norm_eq_abs, abs_of_pos hr] using hr1)).mul_left r⁻¹
  apply hasDerivAt_tsum_of_isPreconnected hgeom Metric.isOpen_ball Metric.isPreconnected_ball
    (t := Metric.ball (0 : ℂ) r)
    (fun n y _ => squaredNativeTerm_hasDerivAt k n y)
    (fun n y hy => squaredNativeDerivative_bound k n hr y
      (by simpa using (Metric.mem_ball.mp hy).le)) (y₀ := (0 : ℂ))
  · simpa using hr
  · exact squaredNativeEuler_summable k 0 (by simp)
  · simpa using hqr

theorem squaredNativeEuler_analyticAt (k : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (squaredNativeEuler k) q := by
  have hd : DifferentiableOn ℂ (squaredNativeEuler k) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact (squaredNativeEuler_hasDerivAt k z (by simpa using hz)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hq))

theorem squaredNativeEuler_succ_eq (k : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    squaredNativeEuler (k + 1) q = q * deriv (squaredNativeEuler k) q := by
  rw [(squaredNativeEuler_hasDerivAt k q hq).deriv, ← tsum_mul_left]
  unfold squaredNativeEuler
  apply tsum_congr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

theorem hadamardEulerIntegral_eq_squaredNativeEuler (k : ℕ) {lambda r : ℝ}
    (hlambda : 0 < lambda) (hlr : lambda < r) (hr1 : r < 1) :
    hadamardEulerIntegral k lambda r = squaredNativeEuler k (lambda : ℂ) :=
  (hadamardEuler_hasSum k hlambda hlr hr1).tsum_eq.symm

theorem angularLoaded_cast_eq_squaredNativeEuler {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (angularLoaded q : ℂ) =
      3192 * squaredNativeEuler 3 (q : ℂ) + 1288 * squaredNativeEuler 2 (q : ℂ) +
        180 * squaredNativeEuler 1 (q : ℂ) + 9 * squaredNativeEuler 0 (q : ℂ) := by
  have hq : ‖(q : ℂ)‖ < 1 := by rwa [Complex.norm_of_nonneg hq0]
  have h3 := (squaredNativeEuler_summable 3 (q : ℂ) hq).hasSum.mul_left (3192 : ℂ)
  have h2 := (squaredNativeEuler_summable 2 (q : ℂ) hq).hasSum.mul_left (1288 : ℂ)
  have h1 := (squaredNativeEuler_summable 1 (q : ℂ) hq).hasSum.mul_left (180 : ℂ)
  have h0 := (squaredNativeEuler_summable 0 (q : ℂ) hq).hasSum.mul_left (9 : ℂ)
  have hc : HasSum (fun n : ℕ => ((coefficient3 n ^ 2 * angularWeight n * q ^ n : ℝ) : ℂ))
      (3192 * squaredNativeEuler 3 (q : ℂ) + 1288 * squaredNativeEuler 2 (q : ℂ) +
        180 * squaredNativeEuler 1 (q : ℂ) + 9 * squaredNativeEuler 0 (q : ℂ)) := by
    apply (((h3.add h2).add h1).add h0).congr_fun
    intro n
    rw [angularWeight_eq_cubic]
    push_cast
    ring
  have hr : HasSum (fun n : ℕ => coefficient3 n ^ 2 * angularWeight n * q ^ n)
      (angularLoaded q) := (angularLoaded_summable hq0 hq1).hasSum
  exact (Complex.hasSum_ofReal.mpr hr).unique hc

theorem angularLoaded_cast_eq_hadamard {lambda r : ℝ}
    (hlambda : 0 < lambda) (hlr : lambda < r) (hr1 : r < 1) :
    (angularLoaded lambda : ℂ) =
      3192 * hadamardEulerIntegral 3 lambda r + 1288 * hadamardEulerIntegral 2 lambda r +
        180 * hadamardEulerIntegral 1 lambda r + 9 * hadamardEulerIntegral 0 lambda r := by
  rw [angularLoaded_cast_eq_squaredNativeEuler hlambda.le (hlr.trans hr1)]
  rw [hadamardEulerIntegral_eq_squaredNativeEuler 3 hlambda hlr hr1,
    hadamardEulerIntegral_eq_squaredNativeEuler 2 hlambda hlr hr1,
    hadamardEulerIntegral_eq_squaredNativeEuler 1 hlambda hlr hr1,
    hadamardEulerIntegral_eq_squaredNativeEuler 0 hlambda hlr hr1]

end Row12

#print axioms Row12.angularWeight_eq_cubic
#print axioms Row12.coefficient3_sq_le_one
#print axioms Row12.squaredNativeEuler_summable
#print axioms Row12.squaredNativeTerm_hasDerivAt
#print axioms Row12.squaredNativeDerivative_bound
#print axioms Row12.squaredNativeEuler_hasDerivAt
#print axioms Row12.squaredNativeEuler_analyticAt
#print axioms Row12.squaredNativeEuler_succ_eq
#print axioms Row12.hadamardEulerIntegral_eq_squaredNativeEuler
#print axioms Row12.angularLoaded_cast_eq_squaredNativeEuler
#print axioms Row12.angularLoaded_cast_eq_hadamard
