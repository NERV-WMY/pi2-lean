import Row12.BetaMoments
import Mathlib.Algebra.BigOperators.Intervals

namespace Row12

noncomputable def betaNormalizer (a : ℝ) : ℝ :=
  Real.Gamma a * Real.Gamma (1 - a)

noncomputable def fiveBetaNormalizer : ℝ :=
  ∏ j ∈ Finset.Icc (1 : ℕ) 5, betaNormalizer ((j : ℝ) / 6)

theorem betaNormalizer_one_sub (a : ℝ) :
    betaNormalizer (1 - a) = betaNormalizer a := by
  unfold betaNormalizer
  rw [show 1 - (1 - a) = a by ring]
  exact mul_comm _ _

theorem betaNormalizer_one_sixth : betaNormalizer (1 / 6) = 2 * Real.pi := by
  rw [betaNormalizer, Real.Gamma_mul_Gamma_one_sub,
    show Real.pi * (1 / 6) = Real.pi / 6 by ring, Real.sin_pi_div_six]
  ring

theorem betaNormalizer_one_third_sq :
    betaNormalizer (1 / 3) ^ 2 = 4 * Real.pi ^ 2 / 3 := by
  rw [betaNormalizer, Real.Gamma_mul_Gamma_one_sub,
    show Real.pi * (1 / 3) = Real.pi / 3 by ring, Real.sin_pi_div_three,
    div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem betaNormalizer_one_half : betaNormalizer (1 / 2) = Real.pi := by
  rw [betaNormalizer, Real.Gamma_mul_Gamma_one_sub,
    show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two, div_one]

theorem fiveBetaNormalizer_eq : fiveBetaNormalizer = 16 * Real.pi ^ 5 / 3 := by
  have h4 : betaNormalizer (2 / 3) = betaNormalizer (1 / 3) := by
    rw [show (2 / 3 : ℝ) = 1 - 1 / 3 by norm_num, betaNormalizer_one_sub]
  have h5 : betaNormalizer (5 / 6) = betaNormalizer (1 / 6) := by
    rw [show (5 / 6 : ℝ) = 1 - 1 / 6 by norm_num, betaNormalizer_one_sub]
  calc
    fiveBetaNormalizer =
        betaNormalizer (1 / 6) * betaNormalizer (1 / 3) * betaNormalizer (1 / 2) *
          betaNormalizer (1 / 3) * betaNormalizer (1 / 6) := by
      norm_num [fiveBetaNormalizer, Finset.prod_Icc_succ_top]
      rw [h4, h5]
    _ = betaNormalizer (1 / 6) ^ 2 * betaNormalizer (1 / 3) ^ 2 *
        betaNormalizer (1 / 2) := by ring
    _ = 16 * Real.pi ^ 5 / 3 := by
      rw [betaNormalizer_one_sixth, betaNormalizer_one_third_sq, betaNormalizer_one_half]
      ring

theorem fiveBetaNormalizer_pos : 0 < fiveBetaNormalizer := by
  rw [fiveBetaNormalizer_eq]
  positivity

end Row12

#print axioms Row12.betaNormalizer_one_sub
#print axioms Row12.betaNormalizer_one_sixth
#print axioms Row12.betaNormalizer_one_third_sq
#print axioms Row12.betaNormalizer_one_half
#print axioms Row12.fiveBetaNormalizer_eq
#print axioms Row12.fiveBetaNormalizer_pos
