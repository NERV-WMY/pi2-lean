import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

open MeasureTheory Set intervalIntegral

namespace Row12

noncomputable def gammaMoment (a : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma (a + n) / (Real.Gamma a * (Nat.factorial n : ℝ))

noncomputable def realBeta (u v : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)

noncomputable def betaKernel (a x : ℝ) : ℝ :=
  x ^ (a - 1) * (1 - x) ^ (-a)

noncomputable def betaDensity (a x : ℝ) : ℝ :=
  betaKernel a x / (Real.Gamma a * Real.Gamma (1 - a))

theorem gammaMoment_zero {a : ℝ} (ha : 0 < a) : gammaMoment a 0 = 1 := by
  simp [gammaMoment, (Real.Gamma_pos_of_pos ha).ne']

theorem gammaMoment_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < gammaMoment a n := by
  exact div_pos (Real.Gamma_pos_of_pos (by positivity))
    (mul_pos (Real.Gamma_pos_of_pos ha) (by positivity))

theorem gammaMoment_succ {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ((n : ℝ) + 1) * gammaMoment a (n + 1) = ((n : ℝ) + a) * gammaMoment a n := by
  have hga : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have han : a + (n : ℝ) ≠ 0 := by positivity
  simp only [gammaMoment, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show a + ((n : ℝ) + 1) = (a + (n : ℝ)) + 1 by ring,
    Real.Gamma_add_one han]
  field_simp [hga, hfac, hn]
  ring

theorem gammaMoment_le_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    gammaMoment a n ≤ 1 := by
  induction n with
  | zero => rw [gammaMoment_zero ha]
  | succ n ih =>
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mp
    rw [gammaMoment_succ ha n]
    calc
      ((n : ℝ) + a) * gammaMoment a n ≤ ((n : ℝ) + a) * 1 :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ ((n : ℝ) + 1) * 1 := by linarith

theorem gammaMoment_eq_ascPochhammer {a : ℝ} (ha : 0 < a) (n : ℕ) :
    gammaMoment a n = (ascPochhammer ℝ n).eval a / (Nat.factorial n : ℝ) := by
  induction n with
  | zero => simp [gammaMoment_zero ha]
  | succ n ih =>
    have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    apply (mul_left_cancel₀ hn)
    rw [gammaMoment_succ ha n, ih, ascPochhammer_succ_eval, Nat.factorial_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hfac, hn]
    ring

private theorem beta_integrand_cast (u v x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ((x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ) : ℂ) =
      (x : ℂ) ^ ((u : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v : ℂ) - 1) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx (u - 1),
    Complex.ofReal_cpow (sub_nonneg.mpr hx1) (v - 1)]
  push_cast
  rfl

theorem complexBeta_eq_realBeta (u v : ℝ) :
    Complex.betaIntegral (u : ℂ) (v : ℂ) = (realBeta u v : ℂ) := by
  calc
    Complex.betaIntegral (u : ℂ) (v : ℂ) =
        ∫ x : ℝ in 0..1, ((x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ) : ℂ) := by
      unfold Complex.betaIntegral
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      exact (beta_integrand_cast u v x hx.1 hx.2).symm
    _ = (realBeta u v : ℂ) := intervalIntegral.integral_ofReal

theorem realBeta_integrable {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (fun x : ℝ => x ^ (u - 1) * (1 - x) ^ (v - 1)) volume 0 1 := by
  have hc := Complex.betaIntegral_convergent
    (u := (u : ℂ)) (v := (v : ℂ)) (by simpa using hu) (by simpa using hv)
  have hr : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) ^ ((u : ℂ) - 1) *
        (1 - (x : ℂ)) ^ ((v : ℂ) - 1)).re) volume 0 1 := ⟨hc.1.re, hc.2.re⟩
  apply hr.congr_uIoo
  intro x hx
  rw [uIoo_of_lt zero_lt_one] at hx
  change ((x : ℂ) ^ ((u : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v : ℂ) - 1)).re = _
  rw [← beta_integrand_cast u v x hx.1.le hx.2.le, Complex.ofReal_re]

theorem realBeta_eq_gamma {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    realBeta u v = Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  apply Complex.ofReal_injective
  rw [← complexBeta_eq_realBeta, Complex.betaIntegral_eq_Gamma_mul_div
    _ _ (by simpa using hu) (by simpa using hv), ← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_mul, Complex.ofReal_div]

theorem realBeta_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : 0 < realBeta u v := by
  rw [realBeta_eq_gamma hu hv]
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos hu) (Real.Gamma_pos_of_pos hv))
    (Real.Gamma_pos_of_pos (add_pos hu hv))

theorem realBeta_one_sub {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    realBeta a (1 - a) = Real.Gamma a * Real.Gamma (1 - a) := by
  rw [realBeta_eq_gamma ha (sub_pos.mpr ha1),
    show a + (1 - a) = 1 by ring, Real.Gamma_one, div_one]

theorem gammaMoment_eq_beta_ratio {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    gammaMoment a n = realBeta (a + n) (1 - a) / realBeta a (1 - a) := by
  rw [realBeta_eq_gamma (by positivity) (sub_pos.mpr ha1), realBeta_one_sub ha ha1,
    show a + (n : ℝ) + (1 - a) = (n : ℝ) + 1 by ring,
    Real.Gamma_nat_eq_factorial, gammaMoment]
  have hga : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hgb : Real.Gamma (1 - a) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr ha1)).ne'
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hga, hgb, hfac]

private theorem beta_moment_integrand {a x : ℝ} (n : ℕ) (hx : 0 < x) :
    x ^ (a + (n : ℝ) - 1) * (1 - x) ^ ((1 - a) - 1) =
      x ^ n * betaKernel a x := by
  rw [show a + (n : ℝ) - 1 = (a - 1) + (n : ℝ) by ring,
    Real.rpow_add hx, Real.rpow_natCast, show (1 - a) - 1 = -a by ring]
  unfold betaKernel
  ring

theorem betaKernel_moment_integrable {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ n * betaKernel a x) volume 0 1 := by
  apply (realBeta_integrable (u := a + n) (by positivity) (sub_pos.mpr ha1)).congr_uIoo
  intro x hx
  rw [uIoo_of_lt zero_lt_one] at hx
  exact beta_moment_integrand n hx.1

theorem betaKernel_moment_integral {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n * betaKernel a x) /
      (Real.Gamma a * Real.Gamma (1 - a)) = gammaMoment a n := by
  rw [gammaMoment_eq_beta_ratio ha ha1, realBeta_one_sub ha ha1]
  congr 1
  unfold realBeta
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro x hx
  exact (beta_moment_integrand n hx.1).symm

theorem betaDensity_moment_integrable {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ n * betaDensity a x) volume 0 1 := by
  simpa only [betaDensity, mul_div_assoc] using
    (betaKernel_moment_integrable ha ha1 n).div_const
      (Real.Gamma a * Real.Gamma (1 - a))

theorem betaDensity_moment_integral {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n * betaDensity a x) = gammaMoment a n := by
  simp only [betaDensity, ← mul_div_assoc, intervalIntegral.integral_div]
  exact betaKernel_moment_integral ha ha1 n

theorem betaDensity_integral {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∫ x : ℝ in 0..1, betaDensity a x) = 1 := by
  simpa only [pow_zero, one_mul, gammaMoment_zero ha] using
    betaDensity_moment_integral ha ha1 0

theorem betaDensity_nonneg {a x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ betaDensity a x := by
  unfold betaDensity betaKernel
  exact div_nonneg
    (mul_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg (sub_nonneg.mpr hx1) _))
    (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos (sub_pos.mpr ha1))).le

end Row12

#print axioms Row12.gammaMoment_zero
#print axioms Row12.gammaMoment_pos
#print axioms Row12.gammaMoment_succ
#print axioms Row12.gammaMoment_le_one
#print axioms Row12.gammaMoment_eq_ascPochhammer
#print axioms Row12.complexBeta_eq_realBeta
#print axioms Row12.realBeta_integrable
#print axioms Row12.realBeta_eq_gamma
#print axioms Row12.realBeta_pos
#print axioms Row12.realBeta_one_sub
#print axioms Row12.gammaMoment_eq_beta_ratio
#print axioms Row12.betaKernel_moment_integrable
#print axioms Row12.betaKernel_moment_integral
#print axioms Row12.betaDensity_moment_integrable
#print axioms Row12.betaDensity_moment_integral
#print axioms Row12.betaDensity_integral
#print axioms Row12.betaDensity_nonneg
