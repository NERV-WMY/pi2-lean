import Row12.Convergence
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.BigOperators.Intervals

namespace Row12

noncomputable def successorProduct (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (1 : ℕ) 5, ((n : ℝ) + (j : ℝ) / 6)

noncomputable def risingProduct (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (1 : ℕ) 5, (ascPochhammer ℝ n).eval ((j : ℝ) / 6)

theorem coefficient_zero : coefficient 0 = 1 := by
  norm_num [coefficient]

theorem successorProduct_eq (n : ℕ) :
    successorProduct n =
      ((n : ℝ) + 1 / 6) * ((n : ℝ) + 2 / 6) * ((n : ℝ) + 3 / 6) *
        ((n : ℝ) + 4 / 6) * ((n : ℝ) + 5 / 6) := by
  unfold successorProduct
  norm_num [Finset.prod_Icc_succ_top]

theorem factorial_six_step (n : ℕ) :
    (Nat.factorial (6 * (n + 1)) : ℝ) =
      (Nat.factorial (6 * n) : ℝ) * (6 * (n : ℝ) + 1) * (6 * (n : ℝ) + 2) *
        (6 * (n : ℝ) + 3) * (6 * (n : ℝ) + 4) * (6 * (n : ℝ) + 5) *
        (6 * (n : ℝ) + 6) := by
  have hnat : Nat.factorial (6 * (n + 1)) =
      Nat.factorial (6 * n) * (6 * n + 1).ascFactorial 6 := by
    rw [Nat.factorial_mul_ascFactorial]
    congr 1
  have hcast : (Nat.factorial (6 * (n + 1)) : ℝ) =
      (Nat.factorial (6 * n) : ℝ) * ((6 * n + 1).ascFactorial 6 : ℝ) := by
    exact_mod_cast hnat
  rw [hcast]
  norm_num [Nat.ascFactorial]
  ring

theorem coefficient_succ_mul (n : ℕ) :
    ((n : ℝ) + 1) ^ 5 * coefficient (n + 1) =
      rho * successorProduct n * coefficient n := by
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold coefficient
  rw [factorial_six_step, Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show 6 * (n + 1) = 6 * n + 6 by omega, pow_add, successorProduct_eq]
  unfold rho
  field_simp [hf, hn]
  ring

theorem coefficient_succ (n : ℕ) :
    coefficient (n + 1) =
      rho * successorProduct n / ((n : ℝ) + 1) ^ 5 * coefficient n := by
  have hn : ((n : ℝ) + 1) ^ 5 ≠ 0 := by positivity
  apply (mul_left_cancel₀ hn)
  rw [coefficient_succ_mul]
  field_simp

theorem risingProduct_zero : risingProduct 0 = 1 := by
  simp [risingProduct]

theorem risingProduct_succ (n : ℕ) :
    risingProduct (n + 1) = risingProduct n * successorProduct n := by
  unfold risingProduct successorProduct
  simp only [ascPochhammer_succ_eval]
  rw [Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  ring

theorem coefficient_eq_risingProduct (n : ℕ) :
    coefficient n = rho ^ n * risingProduct n / (Nat.factorial n : ℝ) ^ 5 := by
  induction n with
  | zero => simp [coefficient_zero, risingProduct_zero]
  | succ n ih =>
    have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [coefficient_succ, ih, risingProduct_succ, Nat.factorial_succ, pow_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hf, hn]
    ring

end Row12

#print axioms Row12.coefficient_zero
#print axioms Row12.successorProduct_eq
#print axioms Row12.factorial_six_step
#print axioms Row12.coefficient_succ_mul
#print axioms Row12.coefficient_succ
#print axioms Row12.risingProduct_zero
#print axioms Row12.risingProduct_succ
#print axioms Row12.coefficient_eq_risingProduct
