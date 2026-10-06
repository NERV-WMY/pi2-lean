import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Row12

noncomputable def coefficient (n : ℕ) : ℝ :=
  (Nat.factorial (6 * n) : ℝ) / (Nat.factorial n : ℝ) ^ 6 / (10 : ℝ) ^ (6 * n)

noncomputable def weight (n : ℕ) : ℝ :=
  532 * (n : ℝ) ^ 2 + 126 * (n : ℝ) + 9

noncomputable def term (n : ℕ) : ℝ :=
  (Nat.factorial (6 * n) : ℝ) / (Nat.factorial n : ℝ) ^ 6 *
    (532 * (n : ℝ) ^ 2 + 126 * (n : ℝ) + 9) / (10 : ℝ) ^ (6 * n)

noncomputable def rho : ℝ := 729 / 15625

theorem factorial_bound (n : ℕ) :
    Nat.factorial (6 * n) ≤ 6 ^ (6 * n) * (Nat.factorial n) ^ 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (6 * n + 1).ascFactorial 6 ≤ (6 * n + 6) ^ 6 :=
      Nat.ascFactorial_le_pow_add (6 * n) 6
    calc
      Nat.factorial (6 * (n + 1)) =
          Nat.factorial (6 * n) * (6 * n + 1).ascFactorial 6 := by
        rw [Nat.factorial_mul_ascFactorial]
        congr 1
      _ ≤ Nat.factorial (6 * n) * (6 * n + 6) ^ 6 := Nat.mul_le_mul_left _ hstep
      _ ≤ (6 ^ (6 * n) * (Nat.factorial n) ^ 6) * (6 * n + 6) ^ 6 :=
        Nat.mul_le_mul_right _ ih
      _ = 6 ^ (6 * (n + 1)) * (Nat.factorial (n + 1)) ^ 6 := by
        rw [show 6 * (n + 1) = 6 * n + 6 by omega, pow_add, Nat.factorial_succ]
        ring

theorem coefficient_nonneg (n : ℕ) : 0 ≤ coefficient n := by
  unfold coefficient
  positivity

theorem coefficient_le_geometric (n : ℕ) : coefficient n ≤ rho ^ n := by
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) ^ 6 := by positivity
  have hbound : (Nat.factorial (6 * n) : ℝ) / (Nat.factorial n : ℝ) ^ 6 ≤
      (6 : ℝ) ^ (6 * n) := by
    apply (div_le_iff₀ hfac).2
    exact_mod_cast factorial_bound n
  calc
    coefficient n ≤ (6 : ℝ) ^ (6 * n) / (10 : ℝ) ^ (6 * n) := by
      exact div_le_div_of_nonneg_right hbound (by positivity)
    _ = rho ^ n := by
      rw [pow_mul, pow_mul, ← div_pow]
      norm_num [rho]

theorem term_eq_coefficient_mul_weight (n : ℕ) : term n = coefficient n * weight n := by
  unfold term coefficient weight
  ring

theorem term_nonneg (n : ℕ) : 0 ≤ term n := by
  unfold term
  positivity

theorem term_summable : Summable term := by
  have hr : ‖rho‖ < 1 := by norm_num [rho, Real.norm_eq_abs]
  have h2 := (summable_pow_mul_geometric_of_norm_lt_one 2 hr).mul_left (532 : ℝ)
  have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left (126 : ℝ)
  have h0 := (summable_geometric_of_norm_lt_one hr).mul_left (9 : ℝ)
  have hmajor : Summable (fun n : ℕ => weight n * rho ^ n) := by
    exact ((h2.add h1).add h0).congr (fun n => by
      simp only [weight, pow_one]
      ring)
  apply Summable.of_nonneg_of_le term_nonneg _ hmajor
  intro n
  rw [term_eq_coefficient_mul_weight]
  have hw : 0 ≤ weight n := by unfold weight; positivity
  nlinarith [coefficient_le_geometric n]

theorem term_hasSum : HasSum term (∑' n : ℕ, term n) := term_summable.hasSum

end Row12
