import Row12.GaussSeries
import Row12.Integral
import Row12.Normalization
import Mathlib.Analysis.Analytic.Binomial

open MeasureTheory Set intervalIntegral
open scoped ENNReal NNReal Interval

namespace Row12

theorem gammaMoment_eq_choose {a : ℝ} (ha : 0 < a) (n : ℕ) :
    gammaMoment a n = Ring.choose (a + n - 1) n := by
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hc := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval, Ring.multichoose_eq] at hc
  rw [gammaMoment_eq_ascPochhammer ha n]
  apply (div_eq_iff hf).2
  simpa only [mul_comm] using hc.symm

theorem gammaMoment_binomial_hasSum {a z : ℝ} (ha : 0 < a) (hz : |z| < 1) :
    HasSum (fun n : ℕ => gammaMoment a n * z ^ n) ((1 - z) ^ (-a)) := by
  have hnn : ‖z‖₊ < (1 : ℝ≥0) := by
    exact_mod_cast (show ‖z‖ < 1 by simpa only [Real.norm_eq_abs] using hz)
  have he : ‖z‖ₑ < (1 : ℝ≥0∞) := by
    simpa only [ENNReal.coe_one] using (enorm_lt_coe).2 hnn
  have hs := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum_sub
    (show z ∈ Metric.eball (0 : ℝ) 1 by simpa using he)
  simp only [sub_zero, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    one_div] at hs
  rw [← Real.rpow_neg (by linarith [le_abs_self z] : 0 ≤ 1 - z) a] at hs
  exact hs.congr_fun (fun n => by rw [gammaMoment_eq_choose ha n])

theorem gammaMoment_add_one {a : ℝ} (ha : 0 < a) (n : ℕ) :
    a * gammaMoment (a + 1) n = ((n : ℝ) + a) * gammaMoment a n := by
  have hga : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have han : a + (n : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  unfold gammaMoment
  rw [show a + 1 + (n : ℝ) = (a + (n : ℝ)) + 1 by ring,
    Real.Gamma_add_one han, Real.Gamma_add_one ha.ne']
  field_simp [hga, hf, ha.ne']
  ring

private theorem shifted_betaAverage_hasSum {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (hAsum : Summable A) :
    HasSum (fun n : ℕ => A n * gammaMoment a (n + 1))
      (betaAverage a (fun x : ℝ => x * ∑' n : ℕ, A n * x ^ n)) := by
  let B : ℕ → ℝ := fun n => if n = 0 then 0 else A (n - 1)
  have hB (n : ℕ) : 0 ≤ B n := by
    dsimp [B]
    split_ifs
    · exact le_refl 0
    · exact hA _
  have hBs : Summable B := (summable_nat_add_iff 1).1 (by simpa [B] using hAsum)
  have hh := hasSum_betaAverage ha ha1 B hB hBs
  have hval : betaAverage a (fun x : ℝ => ∑' n : ℕ, B n * x ^ n) =
      betaAverage a (fun x : ℝ => x * ∑' n : ℕ, A n * x ^ n) := by
    apply betaAverage_congr_Ioo
    intro x hx
    have hpoint : Summable (fun n : ℕ => B n * x ^ n) := by
      apply Summable.of_nonneg_of_le (fun n => mul_nonneg (hB n) (pow_nonneg hx.1.le n)) _ hBs
      intro n
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hx.1.le hx.2.le) (hB n)).trans_eq
        (mul_one _)
    rw [hpoint.tsum_eq_zero_add]
    simp only [B, if_pos rfl, zero_mul, zero_add, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_succ]
    ring
  rw [hval] at hh
  have ht : HasSum (fun n : ℕ => B (n + 1) * gammaMoment a (n + 1))
      (betaAverage a (fun x : ℝ => x * ∑' n : ℕ, A n * x ^ n)) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => B n * gammaMoment a n) 1).2
    simpa [B] using hh
  simpa [B] using ht

theorem betaNormalizer_five_sixths : betaNormalizer (5 / 6) = 2 * Real.pi := by
  rw [show (5 / 6 : ℝ) = 1 - 1 / 6 by norm_num, betaNormalizer_one_sub,
    betaNormalizer_one_sixth]

theorem betaDensity_five_sixths (x : ℝ) :
    betaDensity (5 / 6) x = x ^ (-1 / 6 : ℝ) * (1 - x) ^ (-5 / 6 : ℝ) /
      (2 * Real.pi) := by
  unfold betaDensity betaKernel
  rw [← betaNormalizer, betaNormalizer_five_sixths]
  norm_num

private theorem eulerFactor_continuousOn {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (b : ℝ) :
    ContinuousOn (fun x : ℝ => (1 - p * x) ^ b) [[(0 : ℝ), 1]] := by
  apply (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn.rpow_const
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  have hpx : p * x < 1 :=
    ((mul_le_mul_of_nonneg_left hx.2 hp0).trans_eq (mul_one p)).trans_lt hp1
  exact Or.inl (sub_pos.mpr hpx).ne'

theorem gaussEulerIntegrand_integrable {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (b : ℝ) :
    IntervalIntegrable (fun x : ℝ => betaDensity (5 / 6) x * (1 - p * x) ^ b)
      volume 0 1 := by
  have hd := betaDensity_moment_integrable (by norm_num : (0 : ℝ) < 5 / 6)
    (by norm_num) 0
  simp only [pow_zero, one_mul] at hd
  exact hd.mul_continuousOn (eulerFactor_continuousOn hp0 hp1 b)

theorem gaussDerivativeIntegrand_integrable {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    IntervalIntegrable (fun x : ℝ =>
      (1 / 6 : ℝ) * x * betaDensity (5 / 6) x * (1 - p * x) ^ (-7 / 6 : ℝ))
      volume 0 1 := by
  have hd := betaDensity_moment_integrable (by norm_num : (0 : ℝ) < 5 / 6)
    (by norm_num) 1
  simp only [pow_one] at hd
  simpa only [mul_assoc] using
    (hd.mul_continuousOn (eulerFactor_continuousOn hp0 hp1 (-7 / 6))).const_mul (1 / 6 : ℝ)

theorem gaussA_eq_eulerIntegral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    gaussA p = ∫ x : ℝ in 0..1, betaDensity (5 / 6) x * (1 - p * x) ^ (-1 / 6 : ℝ) := by
  have hp : |p| < 1 := by rwa [abs_of_nonneg hp0]
  let A : ℕ → ℝ := fun n => gammaMoment (1 / 6) n * p ^ n
  have hA (n : ℕ) : 0 ≤ A n :=
    mul_nonneg (gammaMoment_pos (by norm_num) n).le (pow_nonneg hp0 n)
  have hAs : Summable A :=
    (gammaMoment_binomial_hasSum (by norm_num : (0 : ℝ) < 1 / 6) hp).summable
  have hs := hasSum_betaAverage (by norm_num : (0 : ℝ) < 5 / 6) (by norm_num) A hA hAs
  have hval : betaAverage (5 / 6) (fun x : ℝ => ∑' n : ℕ, A n * x ^ n) =
      ∫ x : ℝ in 0..1, betaDensity (5 / 6) x * (1 - p * x) ^ (-1 / 6 : ℝ) := by
    unfold betaAverage
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro x hx
    have hpx0 : 0 ≤ p * x := mul_nonneg hp0 hx.1.le
    have hpx1 : p * x < 1 :=
      ((mul_le_mul_of_nonneg_left hx.2.le hp0).trans_eq (mul_one p)).trans_lt hp1
    have hh : HasSum (fun n : ℕ => gammaMoment (1 / 6) n * (p * x) ^ n)
        ((1 - p * x) ^ (-1 / 6 : ℝ)) := by
      simpa only [neg_div] using gammaMoment_binomial_hasSum
        (by norm_num : (0 : ℝ) < 1 / 6) (by rwa [abs_of_nonneg hpx0] : |p * x| < 1)
    have he : (∑' n : ℕ, A n * x ^ n) = (1 - p * x) ^ (-1 / 6 : ℝ) := by
      rw [← hh.tsum_eq]
      apply tsum_congr
      intro n
      dsimp [A]
      rw [mul_pow]
      ring
    dsimp only
    rw [he]
    exact mul_comm _ _
  rw [hval] at hs
  have hg : HasSum (fun n : ℕ => gaussCoefficient n * p ^ n) (gaussA p) := by
    have hg := (gaussEuler_summable 0 p (by simpa only [Real.norm_eq_abs] using hp)).hasSum
    simpa only [gaussA_eq_tsum, RCLike.ofReal_real_eq_id, id_eq, pow_zero, mul_one] using hg
  apply hg.unique
  apply hs.congr_fun
  intro n
  dsimp [A, gaussCoefficient]
  ring

private theorem gaussDerivative_coefficient (n : ℕ) :
    (1 / 6 : ℝ) * gammaMoment (7 / 6) n * gammaMoment (5 / 6) (n + 1) =
      gaussCoefficient (n + 1) * ((n : ℝ) + 1) := by
  have ha := gammaMoment_add_one (by norm_num : (0 : ℝ) < 1 / 6) n
  rw [show (1 / 6 : ℝ) + 1 = 7 / 6 by norm_num] at ha
  rw [ha, ← gammaMoment_succ (by norm_num : (0 : ℝ) < 1 / 6) n]
  unfold gaussCoefficient
  ring

theorem gaussA_deriv_eq_eulerIntegral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    deriv (gaussA : ℝ → ℝ) p = ∫ x : ℝ in 0..1,
      (1 / 6 : ℝ) * x * betaDensity (5 / 6) x * (1 - p * x) ^ (-7 / 6 : ℝ) := by
  have hp : |p| < 1 := by rwa [abs_of_nonneg hp0]
  let A : ℕ → ℝ := fun n => (1 / 6 : ℝ) * gammaMoment (7 / 6) n * p ^ n
  have hA (n : ℕ) : 0 ≤ A n := by
    exact mul_nonneg (mul_nonneg (by norm_num) (gammaMoment_pos (by norm_num) n).le)
      (pow_nonneg hp0 n)
  have hAs : Summable A := by
    simpa only [A, mul_assoc] using
      (gammaMoment_binomial_hasSum (by norm_num : (0 : ℝ) < 7 / 6) hp).summable.mul_left
        (1 / 6 : ℝ)
  have hs := shifted_betaAverage_hasSum (by norm_num : (0 : ℝ) < 5 / 6) (by norm_num)
    A hA hAs
  have hval : betaAverage (5 / 6) (fun x : ℝ => x * ∑' n : ℕ, A n * x ^ n) =
      ∫ x : ℝ in 0..1,
        (1 / 6 : ℝ) * x * betaDensity (5 / 6) x * (1 - p * x) ^ (-7 / 6 : ℝ) := by
    unfold betaAverage
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro x hx
    have hpx0 : 0 ≤ p * x := mul_nonneg hp0 hx.1.le
    have hpx1 : p * x < 1 :=
      ((mul_le_mul_of_nonneg_left hx.2.le hp0).trans_eq (mul_one p)).trans_lt hp1
    have hh : HasSum (fun n : ℕ => gammaMoment (7 / 6) n * (p * x) ^ n)
        ((1 - p * x) ^ (-7 / 6 : ℝ)) := by
      simpa only [neg_div] using gammaMoment_binomial_hasSum
        (by norm_num : (0 : ℝ) < 7 / 6) (by rwa [abs_of_nonneg hpx0] : |p * x| < 1)
    have he : (∑' n : ℕ, A n * x ^ n) =
        (1 / 6 : ℝ) * (1 - p * x) ^ (-7 / 6 : ℝ) := by
      rw [← hh.tsum_eq, ← tsum_mul_left]
      apply tsum_congr
      intro n
      dsimp [A]
      rw [mul_pow]
      ring
    dsimp only
    rw [he]
    ring
  rw [hval] at hs
  have ht : HasSum (fun n : ℕ => gaussCoefficient (n + 1) * ((n : ℝ) + 1) * p ^ n)
      (∫ x : ℝ in 0..1,
        (1 / 6 : ℝ) * x * betaDensity (5 / 6) x * (1 - p * x) ^ (-7 / 6 : ℝ)) := by
    apply hs.congr_fun
    intro n
    dsimp [A]
    rw [← gaussDerivative_coefficient]
    ring
  have hd : HasDerivAt (gaussEuler 0)
      (∑' n : ℕ, gaussCoefficient n * (n : ℝ) ^ (0 + 1) * p ^ (n - 1)) p := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using
      gaussEuler_hasDerivAt 0 p (by simpa only [Real.norm_eq_abs] using hp)
  rw [gaussEuler_zero_eq] at hd
  rw [hd.deriv]
  have hdt : Summable (fun n : ℕ => gaussCoefficient n * (n : ℝ) ^ (0 + 1) * p ^ (n - 1)) := by
    apply (summable_nat_add_iff 1).1
    simpa only [Nat.zero_add, Nat.cast_add, Nat.cast_one, pow_one, Nat.add_sub_cancel] using ht.summable
  rw [hdt.tsum_eq_zero_add]
  simpa only [Nat.cast_zero, zero_pow (by norm_num : 0 + 1 ≠ 0), mul_zero,
    zero_mul, zero_add, Nat.zero_add, Nat.cast_add, Nat.cast_one, pow_one,
    Nat.add_sub_cancel] using ht.tsum_eq

theorem gaussA_hasDerivAt_eulerIntegral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    HasDerivAt (gaussA : ℝ → ℝ)
      (∫ x : ℝ in 0..1,
        (1 / 6 : ℝ) * x * betaDensity (5 / 6) x * (1 - p * x) ^ (-7 / 6 : ℝ)) p := by
  have h := (gaussA_analyticAt p
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hp0] using hp1)).differentiableAt.hasDerivAt
  rwa [gaussA_deriv_eq_eulerIntegral hp0 hp1] at h

end Row12

#print axioms Row12.gammaMoment_eq_choose
#print axioms Row12.gammaMoment_binomial_hasSum
#print axioms Row12.gammaMoment_add_one
#print axioms Row12.betaNormalizer_five_sixths
#print axioms Row12.betaDensity_five_sixths
#print axioms Row12.gaussEulerIntegrand_integrable
#print axioms Row12.gaussDerivativeIntegrand_integrable
#print axioms Row12.gaussA_eq_eulerIntegral
#print axioms Row12.gaussA_deriv_eq_eulerIntegral
#print axioms Row12.gaussA_hasDerivAt_eulerIntegral
