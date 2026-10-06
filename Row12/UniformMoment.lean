import Row12.Convergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace Row12

noncomputable def uniformMoment (m : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ m

noncomputable def coefficient3 (n : ℕ) : ℝ :=
  (Nat.factorial (6 * n) : ℝ) /
    ((Nat.factorial (3 * n) : ℝ) * (Nat.factorial n : ℝ) ^ 3 * (1728 : ℝ) ^ n)

theorem uniformMoment_integrable (m : ℕ) :
    IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ m) MeasureTheory.volume 0 1 := by
  exact (continuous_const.sub (continuous_id.pow 2)).pow m |>.intervalIntegrable 0 1

theorem uniformMoment_zero : uniformMoment 0 = 1 := by
  simp [uniformMoment, intervalIntegral.integral_const]

theorem uniformPrimitive_hasDerivAt (m : ℕ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => u * (1 - u ^ 2) ^ (m + 1))
      ((2 * (m : ℝ) + 3) * (1 - u ^ 2) ^ (m + 1) -
        (2 * (m : ℝ) + 2) * (1 - u ^ 2) ^ m) u := by
  have hd := (hasDerivAt_id u).mul
    (((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).pow (m + 1))
  apply hd.congr_deriv
  simp only [Pi.pow_apply, Pi.sub_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add,
    Nat.cast_one]
  rw [pow_succ]
  ring

theorem uniformMoment_succ_mul (m : ℕ) :
    (2 * (m : ℝ) + 3) * uniformMoment (m + 1) =
      (2 * (m : ℝ) + 2) * uniformMoment m := by
  have hi1 := (uniformMoment_integrable (m + 1)).const_mul (2 * (m : ℝ) + 3)
  have hi0 := (uniformMoment_integrable m).const_mul (2 * (m : ℝ) + 2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun u _ => uniformPrimitive_hasDerivAt m u) (hi1.sub hi0)
  rw [intervalIntegral.integral_sub hi1 hi0,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
  simp only [one_pow, sub_self, zero_pow (Nat.succ_ne_zero m), mul_zero, zero_mul] at hftc
  exact sub_eq_zero.mp hftc

theorem uniformMoment_eq_factorial (m : ℕ) :
    uniformMoment m =
      (4 : ℝ) ^ m * (Nat.factorial m : ℝ) ^ 2 / (Nat.factorial (2 * m + 1) : ℝ) := by
  induction m with
  | zero => norm_num [uniformMoment_zero]
  | succ m ih =>
    have hf : (Nat.factorial (2 * m + 1) : ℝ) ≠ 0 := by positivity
    have h2 : 2 * (m : ℝ) + 2 ≠ 0 := by positivity
    have h3 : 2 * (m : ℝ) + 3 ≠ 0 := by positivity
    have hfac : (Nat.factorial (2 * (m + 1) + 1) : ℝ) =
        (2 * (m : ℝ) + 3) * (2 * (m : ℝ) + 2) *
          (Nat.factorial (2 * m + 1) : ℝ) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1 + 1) + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    apply mul_left_cancel₀ h3
    rw [uniformMoment_succ_mul, ih, pow_succ, hfac, Nat.factorial_succ m]
    push_cast
    field_simp [hf, h2, h3]
    ring

theorem coefficient3_sq_mul_uniformMoment (n : ℕ) :
    coefficient3 n ^ 2 * uniformMoment (3 * n) =
      ((Nat.factorial (6 * n) : ℝ) /
        ((6 : ℝ) ^ (6 * n) * (Nat.factorial n : ℝ) ^ 6)) / (6 * (n : ℝ) + 1) := by
  have hf6 : (Nat.factorial (6 * n) : ℝ) ≠ 0 := by positivity
  have hf3 : (Nat.factorial (3 * n) : ℝ) ≠ 0 := by positivity
  have hfn : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : 6 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hp : (1728 : ℝ) ^ (n * 2) = (4 : ℝ) ^ (3 * n) * (6 : ℝ) ^ (6 * n) := by
    calc
      (1728 : ℝ) ^ (n * 2) = ((1728 : ℝ) ^ 2) ^ n := by
        rw [show n * 2 = 2 * n by omega, pow_mul]
      _ = ((4 : ℝ) ^ 3 * (6 : ℝ) ^ 6) ^ n := by norm_num
      _ = (4 : ℝ) ^ (3 * n) * (6 : ℝ) ^ (6 * n) := by
        simp only [mul_pow, pow_mul]
  rw [uniformMoment_eq_factorial, show 2 * (3 * n) + 1 = 6 * n + 1 by omega,
    Nat.factorial_succ]
  unfold coefficient3
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    div_pow, mul_pow, ← pow_mul]
  rw [hp]
  field_simp [hf6, hf3, hfn, hn]

end Row12

#print axioms Row12.uniformMoment_integrable
#print axioms Row12.uniformMoment_zero
#print axioms Row12.uniformPrimitive_hasDerivAt
#print axioms Row12.uniformMoment_succ_mul
#print axioms Row12.uniformMoment_eq_factorial
#print axioms Row12.coefficient3_sq_mul_uniformMoment
