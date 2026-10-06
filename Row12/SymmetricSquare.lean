import Row12.NativeSeries
import Row12.BetaMoments
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace Row12

noncomputable def formalTheta (f : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.X * PowerSeries.derivative ℝ f

theorem formalTheta_add (f g : PowerSeries ℝ) :
    formalTheta (f + g) = formalTheta f + formalTheta g := by
  simp [formalTheta, map_add, mul_add]

theorem formalTheta_sub (f g : PowerSeries ℝ) :
    formalTheta (f - g) = formalTheta f - formalTheta g := by
  simp [formalTheta, map_sub, mul_sub]

theorem formalTheta_mul (f g : PowerSeries ℝ) :
    formalTheta (f * g) = f * formalTheta g + g * formalTheta f := by
  simp only [formalTheta, Derivation.leibniz, smul_eq_mul]
  ring

theorem formalTheta_nat (m : ℕ) : formalTheta (m : PowerSeries ℝ) = 0 := by
  simp [formalTheta, Derivation.map_natCast]

theorem formalTheta_X : formalTheta (PowerSeries.X : PowerSeries ℝ) = PowerSeries.X := by
  simp [formalTheta]

theorem formalTheta_C (c : ℝ) : formalTheta (PowerSeries.C c) = 0 := by
  simp [formalTheta]

theorem formalTheta_one : formalTheta (1 : PowerSeries ℝ) = 0 := by
  simp [formalTheta]

theorem formalTheta_coeff (f : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (formalTheta f) = (n : ℝ) * PowerSeries.coeff n f := by
  cases n with
  | zero => simp [formalTheta]
  | succ n =>
    rw [formalTheta, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

noncomputable def formalSecond (g : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.C 144 * ((1-PowerSeries.X) * formalTheta (formalTheta g)) -
    PowerSeries.C 72 * (PowerSeries.X * formalTheta g) -
    PowerSeries.C 5 * (PowerSeries.X * g)

noncomputable def formalThird (f : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.C 72 * ((1-PowerSeries.X) * formalTheta (formalTheta (formalTheta f))) -
    PowerSeries.X * (PowerSeries.C 108 * formalTheta (formalTheta f) +
      PowerSeries.C 46 * formalTheta f + PowerSeries.C 5 * f)

theorem formal_symmetric_square_identity (g : PowerSeries ℝ) :
    formalThird (g^2) = g * formalTheta (formalSecond g) +
      3 * formalTheta g * formalSecond g := by
  simp only [formalThird, formalSecond, pow_two, formalTheta_mul, formalTheta_add,
    formalTheta_sub, formalTheta_C, formalTheta_one, formalTheta_X]
  norm_num only [map_ofNat]
  ring

noncomputable def halfGaussCoefficient (n : ℕ) : ℝ :=
  gammaMoment (1/12) n * gammaMoment (5/12) n

theorem halfGaussCoefficient_zero : halfGaussCoefficient 0 = 1 := by
  norm_num [halfGaussCoefficient, gammaMoment_zero]

theorem halfGaussCoefficient_succ_mul (n : ℕ) :
    ((n : ℝ)+1)^2 * halfGaussCoefficient (n+1) =
      ((n : ℝ)+1/12) * ((n : ℝ)+5/12) * halfGaussCoefficient n := by
  have ha := gammaMoment_succ (by norm_num : (0:ℝ)<1/12) n
  have hb := gammaMoment_succ (by norm_num : (0:ℝ)<5/12) n
  unfold halfGaussCoefficient
  calc
    _ = (((n : ℝ)+1) * gammaMoment (1/12) (n+1)) *
      (((n : ℝ)+1) * gammaMoment (5/12) (n+1)) := by ring
    _ = _ := by rw [ha, hb]; ring

noncomputable def formalHalfGauss : PowerSeries ℝ := PowerSeries.mk halfGaussCoefficient

noncomputable def formalNative : PowerSeries ℝ := PowerSeries.mk coefficient3

private theorem formalSecond_coeff_zero (g : PowerSeries ℝ) :
    PowerSeries.coeff 0 (formalSecond g) = 0 := by
  rw [formalSecond]
  simp only [map_sub, PowerSeries.coeff_C_mul, sub_mul, one_mul,
    PowerSeries.coeff_zero_X_mul, formalTheta_coeff, Nat.cast_zero, zero_mul,
    mul_zero, sub_self]

private theorem formalSecond_coeff_succ (g : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff (n+1) (formalSecond g) =
      144*((n:ℝ)+1)^2 * PowerSeries.coeff (n+1) g -
        (144*(n:ℝ)^2+72*(n:ℝ)+5)*PowerSeries.coeff n g := by
  rw [formalSecond]
  simp only [map_sub, PowerSeries.coeff_C_mul, sub_mul, one_mul,
    PowerSeries.coeff_succ_X_mul, formalTheta_coeff, Nat.cast_add, Nat.cast_one]
  ring

theorem formalHalfGauss_second : formalSecond formalHalfGauss = 0 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [formalSecond_coeff_zero, map_zero]
  | succ n =>
    rw [formalSecond_coeff_succ]
    simp only [formalHalfGauss, PowerSeries.coeff_mk, map_zero]
    have h := halfGaussCoefficient_succ_mul n
    linear_combination (144:ℝ)*h

private theorem formalThird_coeff_zero (f : PowerSeries ℝ) :
    PowerSeries.coeff 0 (formalThird f) = 0 := by
  rw [formalThird]
  simp only [map_sub, PowerSeries.coeff_C_mul, sub_mul, one_mul,
    PowerSeries.coeff_zero_X_mul, formalTheta_coeff, Nat.cast_zero, zero_mul,
    sub_zero, mul_zero]

theorem formalThird_coeff_succ (f : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff (n+1) (formalThird f) =
      72*((n:ℝ)+1)^3 * PowerSeries.coeff (n+1) f -
        (72*(n:ℝ)^3+108*(n:ℝ)^2+46*(n:ℝ)+5)*PowerSeries.coeff n f := by
  rw [formalThird]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, sub_mul, one_mul,
    PowerSeries.coeff_succ_X_mul, formalTheta_coeff, Nat.cast_add, Nat.cast_one]
  ring

theorem formalNative_third : formalThird formalNative = 0 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [formalThird_coeff_zero, map_zero]
  | succ n =>
    rw [formalThird_coeff_succ]
    simp only [formalNative, PowerSeries.coeff_mk, map_zero]
    have h := coefficient3_succ_mul n
    linear_combination (72:ℝ)*h

theorem formalThird_unique {f g : PowerSeries ℝ} (hf : formalThird f = 0)
    (hg : formalThird g = 0) (h0 : PowerSeries.coeff 0 f = PowerSeries.coeff 0 g) : f = g := by
  apply PowerSeries.ext
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hfc := congrArg (PowerSeries.coeff (n+1)) hf
    have hgc := congrArg (PowerSeries.coeff (n+1)) hg
    rw [formalThird_coeff_succ, map_zero] at hfc hgc
    rw [ih] at hfc
    have hnonzero : (72:ℝ)*((n:ℝ)+1)^3 ≠ 0 := by positivity
    apply mul_left_cancel₀ hnonzero
    linarith

theorem formalNative_eq_square : formalNative = formalHalfGauss^2 := by
  apply formalThird_unique formalNative_third
  · rw [formal_symmetric_square_identity, formalHalfGauss_second]
    simp [formalTheta]
  · simp [formalNative, formalHalfGauss, PowerSeries.coeff_mul, pow_two,
      PowerSeries.coeff_mk, coefficient3_zero, halfGaussCoefficient_zero]

theorem nativeCoefficient_clausen (n : ℕ) :
    coefficient3 n = ∑ ij ∈ Finset.antidiagonal n,
      halfGaussCoefficient ij.1 * halfGaussCoefficient ij.2 := by
  have h := congrArg (PowerSeries.coeff n) formalNative_eq_square
  simpa only [formalNative, formalHalfGauss, pow_two, PowerSeries.coeff_mul,
    PowerSeries.coeff_mk] using h

theorem halfGaussCoefficient_pos (n : ℕ) : 0 < halfGaussCoefficient n := by
  exact mul_pos (gammaMoment_pos (by norm_num) n) (gammaMoment_pos (by norm_num) n)

theorem halfGaussCoefficient_le_one (n : ℕ) : halfGaussCoefficient n ≤ 1 := by
  have ha := gammaMoment_le_one (by norm_num : (0:ℝ)<1/12) (by norm_num) n
  have hb := gammaMoment_le_one (by norm_num : (0:ℝ)<5/12) (by norm_num) n
  simpa only [halfGaussCoefficient, one_mul] using
    mul_le_mul ha hb (gammaMoment_pos (by norm_num) n).le zero_le_one

theorem halfGaussCoefficient_eq (n : ℕ) : halfGaussCoefficient n =
    ordinaryHypergeometricCoefficient (1/12:ℝ) (5/12) 1 n := by
  unfold halfGaussCoefficient ordinaryHypergeometricCoefficient
  rw [gammaMoment_eq_ascPochhammer (by norm_num : (0:ℝ)<1/12),
    gammaMoment_eq_ascPochhammer (by norm_num : (0:ℝ)<5/12), ascPochhammer_eval_one]
  ring

section ActualSquare

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem halfPochhammer_cast (a : ℝ) (n : ℕ) :
    (algebraMap ℝ 𝕜) ((ascPochhammer ℝ n).eval a) =
      (ascPochhammer 𝕜 n).eval ((algebraMap ℝ 𝕜) a) := by
  rw [ascPochhammer_eval₂ (algebraMap ℝ 𝕜), Polynomial.eval₂_at_apply]

theorem halfGaussCoefficient_cast (n : ℕ) : (halfGaussCoefficient n : 𝕜) =
    ordinaryHypergeometricCoefficient (1/12:𝕜) (5/12) 1 n := by
  change (algebraMap ℝ 𝕜) (halfGaussCoefficient n) = _
  rw [halfGaussCoefficient_eq]
  simp only [ordinaryHypergeometricCoefficient, map_mul, map_inv₀, map_natCast]
  rw [halfPochhammer_cast (𝕜 := 𝕜) (1/12:ℝ) n,
    halfPochhammer_cast (𝕜 := 𝕜) (5/12:ℝ) n,
    halfPochhammer_cast (𝕜 := 𝕜) 1 n]
  simp only [map_one, map_div₀, map_ofNat]

noncomputable def halfGauss (q : 𝕜) : 𝕜 :=
  ordinaryHypergeometric (1/12:𝕜) (5/12) 1 q

theorem halfGauss_eq_tsum (q : 𝕜) :
    halfGauss q = ∑' n : ℕ, (halfGaussCoefficient n : 𝕜)*q^n := by
  simp only [halfGauss, ordinaryHypergeometric_eq_tsum, smul_eq_mul]
  apply tsum_congr
  intro n
  rw [halfGaussCoefficient_cast]

theorem halfGauss_summable_norm {q : 𝕜} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ‖(halfGaussCoefficient n : 𝕜)*q^n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (summable_geometric_of_norm_lt_one
      (show ‖‖q‖‖ < 1 by simpa only [Real.norm_eq_abs, abs_norm] using hq))
  intro n
  simp only [norm_mul, norm_pow, RCLike.norm_of_nonneg (halfGaussCoefficient_pos n).le]
  exact (mul_le_mul_of_nonneg_right (halfGaussCoefficient_le_one n)
    (pow_nonneg (norm_nonneg q) n)).trans_eq (one_mul _)

theorem nativeF_eq_halfGauss_square (q : 𝕜) (hq : ‖q‖ < 1) :
    nativeF q = halfGauss q ^ 2 := by
  have hs := halfGauss_summable_norm hq
  have hc := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs
  rw [halfGauss_eq_tsum, pow_two, hc, nativeF_eq_tsum]
  symm
  apply tsum_congr
  intro n
  have hcoeff : (coefficient3 n : 𝕜) = ∑ ij ∈ Finset.antidiagonal n,
      (halfGaussCoefficient ij.1 : 𝕜) * (halfGaussCoefficient ij.2 : 𝕜) := by
    have h := congrArg (algebraMap ℝ 𝕜) (nativeCoefficient_clausen n)
    simpa only [map_sum, map_mul] using h
  rw [hcoeff, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hijsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [mul_mul_mul_comm, ← pow_add, hijsum]

end ActualSquare

end Row12

#print axioms Row12.formalTheta_add
#print axioms Row12.formalTheta_sub
#print axioms Row12.formalTheta_mul
#print axioms Row12.formalTheta_nat
#print axioms Row12.formalTheta_X
#print axioms Row12.formalTheta_C
#print axioms Row12.formalTheta_one
#print axioms Row12.formalTheta_coeff
#print axioms Row12.formal_symmetric_square_identity
#print axioms Row12.halfGaussCoefficient_zero
#print axioms Row12.halfGaussCoefficient_succ_mul
#print axioms Row12.formalHalfGauss_second
#print axioms Row12.formalThird_coeff_succ
#print axioms Row12.formalNative_third
#print axioms Row12.formalThird_unique
#print axioms Row12.formalNative_eq_square
#print axioms Row12.nativeCoefficient_clausen
#print axioms Row12.halfGaussCoefficient_pos
#print axioms Row12.halfGaussCoefficient_le_one
#print axioms Row12.halfGaussCoefficient_eq
#print axioms Row12.halfGaussCoefficient_cast
#print axioms Row12.halfGauss_eq_tsum
#print axioms Row12.halfGauss_summable_norm
#print axioms Row12.nativeF_eq_halfGauss_square
