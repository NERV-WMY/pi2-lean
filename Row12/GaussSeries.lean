import Row12.NativeSeries
import Row12.BetaMoments

open scoped ENNReal NNReal

namespace Row12

noncomputable def gaussCoefficient (n : ℕ) : ℝ :=
  gammaMoment (1 / 6) n * gammaMoment (5 / 6) n

theorem gaussCoefficient_eq (n : ℕ) :
    gaussCoefficient n = ordinaryHypergeometricCoefficient (1 / 6 : ℝ) (5 / 6) 1 n := by
  unfold gaussCoefficient ordinaryHypergeometricCoefficient
  rw [gammaMoment_eq_ascPochhammer (by norm_num : (0 : ℝ) < 1 / 6),
    gammaMoment_eq_ascPochhammer (by norm_num : (0 : ℝ) < 5 / 6), ascPochhammer_eval_one]
  ring

theorem gaussCoefficient_zero : gaussCoefficient 0 = 1 := by
  norm_num [gaussCoefficient, gammaMoment_zero]

theorem gaussCoefficient_one : gaussCoefficient 1 = 5 / 36 := by
  rw [gaussCoefficient_eq]
  norm_num [ordinaryHypergeometricCoefficient]

theorem gaussCoefficient_pos (n : ℕ) : 0 < gaussCoefficient n := by
  exact mul_pos (gammaMoment_pos (by norm_num) n) (gammaMoment_pos (by norm_num) n)

theorem gaussCoefficient_le_one (n : ℕ) : gaussCoefficient n ≤ 1 := by
  have ha := gammaMoment_le_one (by norm_num : (0 : ℝ) < 1 / 6) (by norm_num) n
  have hb := gammaMoment_le_one (by norm_num : (0 : ℝ) < 5 / 6) (by norm_num) n
  simpa only [gaussCoefficient, one_mul] using
    mul_le_mul ha hb (gammaMoment_pos (by norm_num) n).le zero_le_one

theorem gaussCoefficient_succ_mul (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 * gaussCoefficient (n + 1) =
      ((n : ℝ) + 1 / 6) * ((n : ℝ) + 5 / 6) * gaussCoefficient n := by
  have ha := gammaMoment_succ (by norm_num : (0 : ℝ) < 1 / 6) n
  have hb := gammaMoment_succ (by norm_num : (0 : ℝ) < 5 / 6) n
  unfold gaussCoefficient
  calc
    _ = (((n : ℝ) + 1) * gammaMoment (1 / 6) (n + 1)) *
        (((n : ℝ) + 1) * gammaMoment (5 / 6) (n + 1)) := by ring
    _ = _ := by rw [ha, hb]; ring

section GaussFunction

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem gaussPochhammer_cast (a : ℝ) (n : ℕ) :
    (algebraMap ℝ 𝕜) ((ascPochhammer ℝ n).eval a) =
      (ascPochhammer 𝕜 n).eval ((algebraMap ℝ 𝕜) a) := by
  rw [ascPochhammer_eval₂ (algebraMap ℝ 𝕜), Polynomial.eval₂_at_apply]

theorem gaussCoefficient_cast (n : ℕ) :
    (gaussCoefficient n : 𝕜) =
      ordinaryHypergeometricCoefficient (1 / 6 : 𝕜) (5 / 6) 1 n := by
  change (algebraMap ℝ 𝕜) (gaussCoefficient n) = _
  rw [gaussCoefficient_eq]
  simp only [ordinaryHypergeometricCoefficient, map_mul, map_inv₀, map_natCast]
  rw [gaussPochhammer_cast (𝕜 := 𝕜) (1 / 6 : ℝ) n,
    gaussPochhammer_cast (𝕜 := 𝕜) (5 / 6 : ℝ) n,
    gaussPochhammer_cast (𝕜 := 𝕜) 1 n]
  simp only [map_one, map_div₀, map_ofNat]

noncomputable def gaussA (p : 𝕜) : 𝕜 := ordinaryHypergeometric (1 / 6 : 𝕜) (5 / 6) 1 p

noncomputable def gaussEuler (k : ℕ) (p : 𝕜) : 𝕜 :=
  ∑' n : ℕ, (gaussCoefficient n : 𝕜) * (n : 𝕜) ^ k * p ^ n

theorem gaussA_eq_tsum (p : 𝕜) : gaussA p = ∑' n : ℕ, (gaussCoefficient n : 𝕜) * p ^ n := by
  simp only [gaussA, ordinaryHypergeometric_eq_tsum, smul_eq_mul]
  apply tsum_congr
  intro n
  rw [gaussCoefficient_cast]

theorem gaussEuler_zero_eq : gaussEuler 0 = (gaussA : 𝕜 → 𝕜) := by
  funext p
  simp [gaussEuler, gaussA_eq_tsum]

theorem gaussA_zero : gaussA (0 : 𝕜) = 1 := by
  simp [gaussA]

theorem gaussEuler_summable (k : ℕ) (p : 𝕜) (hp : ‖p‖ < 1) :
    Summable (fun n : ℕ => (gaussCoefficient n : 𝕜) * (n : 𝕜) ^ k * p ^ n) := by
  have hr : ‖‖p‖‖ < 1 := by simpa only [Real.norm_eq_abs, abs_norm] using hp
  apply (summable_pow_mul_geometric_of_norm_lt_one k hr).of_norm_bounded
  intro n
  simp only [norm_mul, norm_pow, RCLike.norm_of_nonneg (gaussCoefficient_pos n).le,
    RCLike.norm_natCast]
  calc
    gaussCoefficient n * (n : ℝ) ^ k * ‖p‖ ^ n ≤ 1 * (n : ℝ) ^ k * ‖p‖ ^ n := by
      gcongr
      exact gaussCoefficient_le_one n
    _ = (n : ℝ) ^ k * ‖p‖ ^ n := by ring

theorem gaussSeries_radius : (1 : ℝ≥0∞) ≤
    (ordinaryHypergeometricSeries 𝕜 (1 / 6 : 𝕜) (5 / 6) 1).radius := by
  apply (ordinaryHypergeometricSeries 𝕜 (1 / 6 : 𝕜) (5 / 6) 1).le_radius_of_bound
    (1 : ℝ) (r := (1 : ℝ≥0))
  intro n
  simp only [ordinaryHypergeometricSeries, FormalMultilinearSeries.ofScalars_norm,
    NNReal.coe_one, one_pow, mul_one, ← gaussCoefficient_cast,
    RCLike.norm_of_nonneg (gaussCoefficient_pos n).le]
  exact gaussCoefficient_le_one n

theorem gaussA_analyticAt (p : 𝕜) (hp : ‖p‖ < 1) : AnalyticAt 𝕜 gaussA p := by
  let s := ordinaryHypergeometricSeries 𝕜 (1 / 6 : 𝕜) (5 / 6) 1
  have hr : (0 : ℝ≥0∞) < s.radius := lt_of_lt_of_le (by norm_num) gaussSeries_radius
  have hpr : ‖p‖ₑ < s.radius := by
    apply lt_of_lt_of_le _ gaussSeries_radius
    have hnn : ‖p‖₊ < (1 : ℝ≥0) := by exact_mod_cast hp
    simpa only [ENNReal.coe_one] using (enorm_lt_coe).2 hnn
  exact (s.hasFPowerSeriesOnBall hr).analyticAt_of_mem
    (show p ∈ Metric.eball (0 : 𝕜) s.radius by simpa using hpr)

theorem gaussTerm_hasDerivAt (k n : ℕ) (p : 𝕜) :
    HasDerivAt (fun p : 𝕜 => (gaussCoefficient n : 𝕜) * (n : 𝕜) ^ k * p ^ n)
      ((gaussCoefficient n : 𝕜) * (n : 𝕜) ^ (k + 1) * p ^ (n - 1)) p := by
  have hd := ((hasDerivAt_id p).pow n).const_mul ((gaussCoefficient n : 𝕜) * (n : 𝕜) ^ k)
  apply hd.congr_deriv
  simp only [id_eq]
  rw [pow_succ]
  ring

theorem gaussDerivative_bound (k n : ℕ) {r : ℝ} (hr : 0 < r) (p : 𝕜) (hp : ‖p‖ ≤ r) :
    ‖(gaussCoefficient n : 𝕜) * (n : 𝕜) ^ (k + 1) * p ^ (n - 1)‖ ≤
      r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n) := by
  simp only [norm_mul, norm_pow, RCLike.norm_of_nonneg (gaussCoefficient_pos n).le,
    RCLike.norm_natCast]
  calc
    gaussCoefficient n * (n : ℝ) ^ (k + 1) * ‖p‖ ^ (n - 1) ≤
        1 * (n : ℝ) ^ (k + 1) * r ^ (n - 1) := by
      gcongr
      exact gaussCoefficient_le_one n
    _ = r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n) := by
      cases n with
      | zero => simp
      | succ n =>
        simp only [Nat.add_sub_cancel, pow_succ]
        field_simp

theorem gaussEuler_hasDerivAt (k : ℕ) (p : 𝕜) (hp : ‖p‖ < 1) :
    HasDerivAt (gaussEuler k)
      (∑' n : ℕ, (gaussCoefficient n : 𝕜) * (n : 𝕜) ^ (k + 1) * p ^ (n - 1)) p := by
  let r : ℝ := (‖p‖ + 1) / 2
  have hr : 0 < r := by dsimp [r]; nlinarith [norm_nonneg p]
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hpr : ‖p‖ < r := by dsimp [r]; linarith
  have hgeom : Summable (fun n : ℕ => r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (k + 1)
      (by simpa only [Real.norm_eq_abs, abs_of_pos hr] using hr1)).mul_left r⁻¹
  apply hasDerivAt_tsum_of_isPreconnected hgeom Metric.isOpen_ball Metric.isPreconnected_ball
    (t := Metric.ball (0 : 𝕜) r)
    (fun n y _ => gaussTerm_hasDerivAt k n y)
    (fun n y hy => gaussDerivative_bound k n hr y (by simpa using (Metric.mem_ball.mp hy).le))
    (y₀ := (0 : 𝕜))
  · simpa using hr
  · exact gaussEuler_summable k 0 (by simp)
  · simpa using hpr

theorem gaussEuler_succ_eq (k : ℕ) (p : 𝕜) (hp : ‖p‖ < 1) :
    gaussEuler (k + 1) p = p * deriv (gaussEuler k) p := by
  rw [(gaussEuler_hasDerivAt k p hp).deriv, ← tsum_mul_left]
  unfold gaussEuler
  apply tsum_congr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

theorem gaussEuler_quadratic (p : 𝕜) (hp : ‖p‖ < 1) :
    gaussEuler 2 p = p * (gaussEuler 2 p + gaussEuler 1 p + (5 / 36 : 𝕜) * gaussEuler 0 p) := by
  have h0 := gaussEuler_summable 0 p hp
  have h1 := gaussEuler_summable 1 p hp
  have h2 := gaussEuler_summable 2 p hp
  have hshift := h2.tsum_eq_zero_add
  simp only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul,
    zero_add] at hshift
  calc
    gaussEuler 2 p = ∑' n : ℕ, (gaussCoefficient (n + 1) : 𝕜) * (n + 1 : 𝕜) ^ 2 * p ^ (n + 1) := by
      simpa only [gaussEuler, Nat.cast_add, Nat.cast_one] using hshift
    _ = p * ∑' n : ℕ, (gaussCoefficient n : 𝕜) *
        ((n : 𝕜) + 1 / 6) * ((n : 𝕜) + 5 / 6) * p ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      have hc : ((n : 𝕜) + 1) ^ 2 * (gaussCoefficient (n + 1) : 𝕜) =
          ((n : 𝕜) + 1 / 6) * ((n : 𝕜) + 5 / 6) * (gaussCoefficient n : 𝕜) := by
        have hc := congrArg (algebraMap ℝ 𝕜) (gaussCoefficient_succ_mul n)
        simpa only [map_mul, map_pow, map_add, map_div₀, map_one, map_ofNat, map_natCast] using hc
      calc
        _ = p * ((((n : 𝕜) + 1) ^ 2 * (gaussCoefficient (n + 1) : 𝕜)) * p ^ n) := by
          rw [pow_succ]
          ring
        _ = _ := by rw [hc]; ring
    _ = p * (gaussEuler 2 p + gaussEuler 1 p + (5 / 36 : 𝕜) * gaussEuler 0 p) := by
      congr 1
      calc
        _ = ∑' n : ℕ, ((gaussCoefficient n : 𝕜) * (n : 𝕜) ^ 2 * p ^ n +
            (gaussCoefficient n : 𝕜) * (n : 𝕜) ^ 1 * p ^ n +
            (5 / 36 : 𝕜) * ((gaussCoefficient n : 𝕜) * (n : 𝕜) ^ 0 * p ^ n)) := by
          apply tsum_congr
          intro n
          ring
        _ = _ := by
          rw [(h2.add h1).tsum_add (h0.mul_left (5 / 36 : 𝕜)), h2.tsum_add h1, tsum_mul_left]
          rfl

theorem gaussA_deriv_zero : deriv (gaussA : 𝕜 → 𝕜) 0 = 5 / 36 := by
  have hd := gaussEuler_hasDerivAt 0 (0 : 𝕜) (by simp)
  rw [gaussEuler_zero_eq] at hd
  rw [hd.deriv]
  calc
    _ = (gaussCoefficient 1 : 𝕜) * ((1 : ℕ) : 𝕜) ^ (0 + 1) *
        (0 : 𝕜) ^ ((1 : ℕ) - 1) := by
      apply tsum_eq_single (1 : ℕ)
      intro n hn
      cases n with
      | zero => simp
      | succ n =>
        cases n with
        | zero => exact (hn rfl).elim
        | succ n => simp
    _ = 5 / 36 := by simp [gaussCoefficient_one, map_ofNat]

theorem gaussA_equation (p : 𝕜) (hp : ‖p‖ < 1) :
    p * (1 - p) * deriv (deriv gaussA) p +
      (1 - 2 * p) * deriv gaussA p - (5 / 36 : 𝕜) * gaussA p = 0 := by
  by_cases hp0 : p = 0
  · simp [hp0, gaussA_zero, gaussA_deriv_zero]
  have ha := gaussA_analyticAt p hp
  have hda := ha.deriv.differentiableAt.hasDerivAt
  have he : gaussEuler 1 =ᶠ[nhds p] (fun z : 𝕜 => z * deriv gaussA z) := by
    have hb : Metric.ball (0 : 𝕜) 1 ∈ nhds p :=
      Metric.isOpen_ball.mem_nhds (by simpa using hp)
    filter_upwards [hb] with z hz
    simpa only [gaussEuler_zero_eq] using gaussEuler_succ_eq 0 z (by simpa using hz)
  have hd1 : deriv (gaussEuler 1) p = deriv gaussA p + p * deriv (deriv gaussA) p := by
    have hd := ((hasDerivAt_id p).mul hda).congr_of_eventuallyEq he
    simpa only [id_eq, one_mul] using hd.deriv
  have h1 : gaussEuler 1 p = p * deriv gaussA p := by
    simpa only [gaussEuler_zero_eq] using gaussEuler_succ_eq 0 p hp
  have h2 : gaussEuler 2 p = p * (deriv gaussA p + p * deriv (deriv gaussA) p) := by
    rw [gaussEuler_succ_eq 1 p hp, hd1]
  have hode := gaussEuler_quadratic p hp
  rw [h2, h1, gaussEuler_zero_eq] at hode
  have hc := mul_left_cancel₀ hp0 hode
  linear_combination hc

end GaussFunction

end Row12

#print axioms Row12.gaussCoefficient_eq
#print axioms Row12.gaussCoefficient_zero
#print axioms Row12.gaussCoefficient_one
#print axioms Row12.gaussCoefficient_pos
#print axioms Row12.gaussCoefficient_le_one
#print axioms Row12.gaussCoefficient_succ_mul
#print axioms Row12.gaussCoefficient_cast
#print axioms Row12.gaussA_eq_tsum
#print axioms Row12.gaussEuler_zero_eq
#print axioms Row12.gaussA_zero
#print axioms Row12.gaussEuler_summable
#print axioms Row12.gaussSeries_radius
#print axioms Row12.gaussA_analyticAt
#print axioms Row12.gaussTerm_hasDerivAt
#print axioms Row12.gaussDerivative_bound
#print axioms Row12.gaussEuler_hasDerivAt
#print axioms Row12.gaussEuler_succ_eq
#print axioms Row12.gaussEuler_quadratic
#print axioms Row12.gaussA_deriv_zero
#print axioms Row12.gaussA_equation
