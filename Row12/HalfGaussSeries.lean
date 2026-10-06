import Row12.SymmetricSquare

open scoped ENNReal NNReal

namespace Row12

variable {𝕜 : Type*} [RCLike 𝕜]
noncomputable def halfEuler (k : ℕ) (p : 𝕜) : 𝕜 :=
  ∑' n : ℕ, (halfGaussCoefficient n : 𝕜) * (n : 𝕜) ^ k * p ^ n

theorem halfEuler_zero_eq : halfEuler 0 = (halfGauss : 𝕜 → 𝕜) := by
  funext p
  simp [halfEuler, halfGauss_eq_tsum]

theorem halfGauss_zero : halfGauss (0 : 𝕜) = 1 := by
  simp [halfGauss]

theorem halfEuler_summable (k : ℕ) (p : 𝕜) (hp : ‖p‖ < 1) :
    Summable (fun n : ℕ => (halfGaussCoefficient n : 𝕜) * (n : 𝕜) ^ k * p ^ n) := by
  have hr : ‖‖p‖‖ < 1 := by simpa only [Real.norm_eq_abs, abs_norm] using hp
  apply (summable_pow_mul_geometric_of_norm_lt_one k hr).of_norm_bounded
  intro n
  simp only [norm_mul, norm_pow, RCLike.norm_of_nonneg (halfGaussCoefficient_pos n).le,
    RCLike.norm_natCast]
  calc
    halfGaussCoefficient n * (n : ℝ) ^ k * ‖p‖ ^ n ≤ 1 * (n : ℝ) ^ k * ‖p‖ ^ n := by
      gcongr
      exact halfGaussCoefficient_le_one n
    _ = (n : ℝ) ^ k * ‖p‖ ^ n := by ring

theorem halfGaussSeries_radius : (1 : ℝ≥0∞) ≤
    (ordinaryHypergeometricSeries 𝕜 (1 / 12 : 𝕜) (5 / 12) 1).radius := by
  apply (ordinaryHypergeometricSeries 𝕜 (1 / 12 : 𝕜) (5 / 12) 1).le_radius_of_bound
    (1 : ℝ) (r := (1 : ℝ≥0))
  intro n
  simp only [ordinaryHypergeometricSeries, FormalMultilinearSeries.ofScalars_norm,
    NNReal.coe_one, one_pow, mul_one, ← halfGaussCoefficient_cast,
    RCLike.norm_of_nonneg (halfGaussCoefficient_pos n).le]
  exact halfGaussCoefficient_le_one n

theorem halfGauss_analyticAt (p : 𝕜) (hp : ‖p‖ < 1) : AnalyticAt 𝕜 halfGauss p := by
  let s := ordinaryHypergeometricSeries 𝕜 (1 / 12 : 𝕜) (5 / 12) 1
  have hr : (0 : ℝ≥0∞) < s.radius := lt_of_lt_of_le (by norm_num) halfGaussSeries_radius
  have hpr : ‖p‖ₑ < s.radius := by
    apply lt_of_lt_of_le _ halfGaussSeries_radius
    have hnn : ‖p‖₊ < (1 : ℝ≥0) := by exact_mod_cast hp
    simpa only [ENNReal.coe_one] using (enorm_lt_coe).2 hnn
  exact (s.hasFPowerSeriesOnBall hr).analyticAt_of_mem
    (show p ∈ Metric.eball (0 : 𝕜) s.radius by simpa using hpr)

theorem halfTerm_hasDerivAt (k n : ℕ) (p : 𝕜) :
    HasDerivAt (fun p : 𝕜 => (halfGaussCoefficient n : 𝕜) * (n : 𝕜) ^ k * p ^ n)
      ((halfGaussCoefficient n : 𝕜) * (n : 𝕜) ^ (k + 1) * p ^ (n - 1)) p := by
  have hd := ((hasDerivAt_id p).pow n).const_mul ((halfGaussCoefficient n : 𝕜) * (n : 𝕜) ^ k)
  apply hd.congr_deriv
  simp only [id_eq]
  rw [pow_succ]
  ring

theorem halfDerivative_bound (k n : ℕ) {r : ℝ} (hr : 0 < r) (p : 𝕜) (hp : ‖p‖ ≤ r) :
    ‖(halfGaussCoefficient n : 𝕜) * (n : 𝕜) ^ (k + 1) * p ^ (n - 1)‖ ≤
      r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n) := by
  simp only [norm_mul, norm_pow, RCLike.norm_of_nonneg (halfGaussCoefficient_pos n).le,
    RCLike.norm_natCast]
  calc
    halfGaussCoefficient n * (n : ℝ) ^ (k + 1) * ‖p‖ ^ (n - 1) ≤
        1 * (n : ℝ) ^ (k + 1) * r ^ (n - 1) := by
      gcongr
      exact halfGaussCoefficient_le_one n
    _ = r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n) := by
      cases n with
      | zero => simp
      | succ n =>
        simp only [Nat.add_sub_cancel, pow_succ]
        field_simp

theorem halfEuler_hasDerivAt (k : ℕ) (p : 𝕜) (hp : ‖p‖ < 1) :
    HasDerivAt (halfEuler k)
      (∑' n : ℕ, (halfGaussCoefficient n : 𝕜) * (n : 𝕜) ^ (k + 1) * p ^ (n - 1)) p := by
  let r : ℝ := (‖p‖ + 1) / 2
  have hr : 0 < r := by dsimp [r]; nlinarith [norm_nonneg p]
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hpr : ‖p‖ < r := by dsimp [r]; linarith
  have hgeom : Summable (fun n : ℕ => r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (k + 1)
      (by simpa only [Real.norm_eq_abs, abs_of_pos hr] using hr1)).mul_left r⁻¹
  apply hasDerivAt_tsum_of_isPreconnected hgeom Metric.isOpen_ball Metric.isPreconnected_ball
    (t := Metric.ball (0 : 𝕜) r)
    (fun n y _ => halfTerm_hasDerivAt k n y)
    (fun n y hy => halfDerivative_bound k n hr y (by simpa using (Metric.mem_ball.mp hy).le))
    (y₀ := (0 : 𝕜))
  · simpa using hr
  · exact halfEuler_summable k 0 (by simp)
  · simpa using hpr

theorem halfEuler_succ_eq (k : ℕ) (p : 𝕜) (hp : ‖p‖ < 1) :
    halfEuler (k + 1) p = p * deriv (halfEuler k) p := by
  rw [(halfEuler_hasDerivAt k p hp).deriv, ← tsum_mul_left]
  unfold halfEuler
  apply tsum_congr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

theorem halfEuler_quadratic (p : 𝕜) (hp : ‖p‖ < 1) :
    halfEuler 2 p = p * (halfEuler 2 p + (1/2:𝕜)*halfEuler 1 p +
      (5/144:𝕜)*halfEuler 0 p) := by
  have h0 := halfEuler_summable 0 p hp
  have h1 := halfEuler_summable 1 p hp
  have h2 := halfEuler_summable 2 p hp
  have hshift := h2.tsum_eq_zero_add
  simp only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul,
    zero_add] at hshift
  calc
    halfEuler 2 p = ∑' n : ℕ, (halfGaussCoefficient (n+1) : 𝕜)*(n+1:𝕜)^2*p^(n+1) := by
      simpa only [halfEuler, Nat.cast_add, Nat.cast_one] using hshift
    _ = p * ∑' n : ℕ, (halfGaussCoefficient n : 𝕜)*
        ((n:𝕜)+1/12)*((n:𝕜)+5/12)*p^n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      have hc : ((n:𝕜)+1)^2*(halfGaussCoefficient (n+1):𝕜) =
          ((n:𝕜)+1/12)*((n:𝕜)+5/12)*(halfGaussCoefficient n:𝕜) := by
        have hc := congrArg (algebraMap ℝ 𝕜) (halfGaussCoefficient_succ_mul n)
        simpa only [map_mul, map_pow, map_add, map_div₀, map_one, map_ofNat, map_natCast] using hc
      calc
        _ = p * ((((n:𝕜)+1)^2*(halfGaussCoefficient (n+1):𝕜))*p^n) := by
          rw [pow_succ]
          ring
        _ = _ := by rw [hc]; ring
    _ = p * (halfEuler 2 p+(1/2:𝕜)*halfEuler 1 p+(5/144:𝕜)*halfEuler 0 p) := by
      congr 1
      calc
        _ = ∑' n : ℕ, ((halfGaussCoefficient n:𝕜)*(n:𝕜)^2*p^n+
            (1/2:𝕜)*((halfGaussCoefficient n:𝕜)*(n:𝕜)^1*p^n)+
            (5/144:𝕜)*((halfGaussCoefficient n:𝕜)*(n:𝕜)^0*p^n)) := by
          apply tsum_congr
          intro n
          ring
        _ = _ := by
          rw [(h2.add (h1.mul_left (1/2:𝕜))).tsum_add (h0.mul_left (5/144:𝕜)),
            h2.tsum_add (h1.mul_left (1/2:𝕜)), tsum_mul_left, tsum_mul_left]
          rfl

theorem halfGauss_deriv_zero : deriv (halfGauss : 𝕜 → 𝕜) 0 = 5/144 := by
  have hd := halfEuler_hasDerivAt 0 (0:𝕜) (by simp)
  rw [halfEuler_zero_eq] at hd
  rw [hd.deriv]
  calc
    _ = (halfGaussCoefficient 1:𝕜)*((1:ℕ):𝕜)^(0+1)*(0:𝕜)^((1:ℕ)-1) := by
      apply tsum_eq_single (1:ℕ)
      intro n hn
      cases n with
      | zero => simp
      | succ n =>
        cases n with
        | zero => exact (hn rfl).elim
        | succ n => simp
    _ = 5/144 := by
      have hcoef : halfGaussCoefficient 1 = 5/144 := by
        rw [halfGaussCoefficient_eq]
        norm_num [ordinaryHypergeometricCoefficient]
      simp [hcoef, map_ofNat]

theorem halfGauss_equation (p : 𝕜) (hp : ‖p‖ < 1) :
    p*(1-p)*deriv (deriv halfGauss) p+
      (1-(3/2:𝕜)*p)*deriv halfGauss p-(5/144:𝕜)*halfGauss p = 0 := by
  by_cases hp0 : p = 0
  · simp [hp0, halfGauss_zero, halfGauss_deriv_zero]
  have ha := halfGauss_analyticAt p hp
  have hda := ha.deriv.differentiableAt.hasDerivAt
  have he : halfEuler 1 =ᶠ[nhds p] (fun z : 𝕜 => z*deriv halfGauss z) := by
    have hb : Metric.ball (0:𝕜) 1 ∈ nhds p :=
      Metric.isOpen_ball.mem_nhds (by simpa using hp)
    filter_upwards [hb] with z hz
    simpa only [halfEuler_zero_eq] using halfEuler_succ_eq 0 z (by simpa using hz)
  have hd1 : deriv (halfEuler 1) p = deriv halfGauss p+p*deriv (deriv halfGauss) p := by
    have hd := ((hasDerivAt_id p).mul hda).congr_of_eventuallyEq he
    simpa only [id_eq, one_mul] using hd.deriv
  have h1 : halfEuler 1 p = p*deriv halfGauss p := by
    simpa only [halfEuler_zero_eq] using halfEuler_succ_eq 0 p hp
  have h2 : halfEuler 2 p = p*(deriv halfGauss p+p*deriv (deriv halfGauss) p) := by
    rw [halfEuler_succ_eq 1 p hp, hd1]
  have hode := halfEuler_quadratic p hp
  rw [h2, h1, halfEuler_zero_eq] at hode
  have hc := mul_left_cancel₀ hp0 hode
  linear_combination hc

end Row12

#print axioms Row12.halfEuler_zero_eq
#print axioms Row12.halfGauss_zero
#print axioms Row12.halfEuler_summable
#print axioms Row12.halfGaussSeries_radius
#print axioms Row12.halfGauss_analyticAt
#print axioms Row12.halfTerm_hasDerivAt
#print axioms Row12.halfDerivative_bound
#print axioms Row12.halfEuler_hasDerivAt
#print axioms Row12.halfEuler_succ_eq
#print axioms Row12.halfEuler_quadratic
#print axioms Row12.halfGauss_deriv_zero
#print axioms Row12.halfGauss_equation
