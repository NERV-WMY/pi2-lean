import Row12.BetaMoments
import Row12.Kernel
import Row12.Coefficient
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set intervalIntegral
open scoped Interval

namespace Row12

noncomputable def betaAverage (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, f x * betaDensity a x

theorem hasSum_betaAverage {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (hAsum : Summable A) :
    HasSum (fun n : ℕ => A n * gammaMoment a n)
      (betaAverage a (fun x : ℝ => ∑' n : ℕ, A n * x ^ n)) := by
  have hint (n : ℕ) : IntervalIntegrable
      (fun x : ℝ => A n * x ^ n * betaDensity a x) volume 0 1 := by
    simpa only [mul_assoc] using
      (betaDensity_moment_integrable ha ha1 n).const_mul (A n)
  have hnonneg (x : ℝ) (hx : x ∈ Ι (0 : ℝ) 1) : 0 ≤ betaDensity a x := by
    rw [uIoc_of_le zero_le_one] at hx
    unfold betaDensity betaKernel
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hx.1.le _)
      (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _))
      (mul_pos (Real.Gamma_pos_of_pos ha)
        (Real.Gamma_pos_of_pos (sub_pos.mpr ha1))).le
  have hp (n : ℕ) (x : ℝ) (hx : x ∈ Ι (0 : ℝ) 1) :
      0 ≤ x ^ n ∧ x ^ n ≤ 1 := by
    rw [uIoc_of_le zero_le_one] at hx
    exact ⟨pow_nonneg hx.1.le _, pow_le_one₀ hx.1.le hx.2⟩
  have hpoint (x : ℝ) (hx : x ∈ Ι (0 : ℝ) 1) :
      Summable (fun n : ℕ => A n * x ^ n) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hA n) (hp n x hx).1) _ hAsum
    intro n
    exact (mul_le_mul_of_nonneg_left (hp n x hx).2 (hA n)).trans_eq (mul_one _)
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := volume)
    (F := fun n x => A n * x ^ n * betaDensity a x)
    (f := fun x => (∑' n : ℕ, A n * x ^ n) * betaDensity a x)
    (fun n x => A n * betaDensity a x)
    (fun n => (hint n).aestronglyMeasurable_restrict_uIoc)
    (fun n => Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_of_nonneg (mul_nonneg
        (mul_nonneg (hA n) (hp n x hx).1) (hnonneg x hx))]
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left (hp n x hx).2 (hA n)).trans_eq (mul_one _))
        (hnonneg x hx)))
    (Filter.Eventually.of_forall (fun x _ => hAsum.mul_right (betaDensity a x)))
    (by
      have hd := (betaDensity_moment_integrable ha ha1 0)
      simp only [pow_zero, one_mul] at hd
      simpa only [tsum_mul_right] using hd.const_mul (∑' n : ℕ, A n))
    (Filter.Eventually.of_forall (fun x hx =>
      (hpoint x hx).hasSum.mul_right (betaDensity a x)))
  have heq (n : ℕ) :
      (∫ x : ℝ in 0..1, A n * x ^ n * betaDensity a x) = A n * gammaMoment a n := by
    simp only [mul_assoc, intervalIntegral.integral_const_mul]
    rw [betaDensity_moment_integral ha ha1 n]
  exact hsum.congr_fun (fun n => (heq n).symm)

noncomputable def momentPrefix (k n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (1 : ℕ) k, gammaMoment ((j : ℝ) / 6) n

noncomputable def nestedKernel : ℕ → ℝ → ℝ
  | 0, r => weightedKernel r
  | k + 1, r => betaAverage (((k + 1 : ℕ) : ℝ) / 6)
      (fun x => nestedKernel k (r * x))

theorem betaAverage_congr_Ioo (a : ℝ) {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Ioo (0 : ℝ) 1, f x = g x) :
    betaAverage a f = betaAverage a g := by
  unfold betaAverage
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro x hx
  dsimp only
  rw [hfg x hx]

theorem momentPrefix_nonneg (k n : ℕ) : 0 ≤ momentPrefix k n := by
  apply Finset.prod_nonneg
  intro j hj
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  exact (gammaMoment_pos (by linarith : 0 < (j : ℝ) / 6) n).le

theorem momentPrefix_le_one {k : ℕ} (hk : k ≤ 5) (n : ℕ) :
    momentPrefix k n ≤ 1 := by
  apply Finset.prod_le_one
  · intro j hj
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    exact (gammaMoment_pos (by linarith : 0 < (j : ℝ) / 6) n).le
  · intro j hj
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hj5 : (j : ℝ) ≤ 5 := by exact_mod_cast ((Finset.mem_Icc.mp hj).2.trans hk)
    exact gammaMoment_le_one (by linarith) (by linarith) n

theorem momentPrefix_succ (k n : ℕ) :
    momentPrefix (k + 1) n = momentPrefix k n * gammaMoment (((k + 1 : ℕ) : ℝ) / 6) n := by
  exact Finset.prod_Icc_succ_top (by omega) _

theorem nestedKernel_hasSum (k : ℕ) (hk : k ≤ 5) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => weight n * r ^ n * momentPrefix k n) (nestedKernel k r) := by
  have hr : |r| < 1 := by rwa [abs_of_nonneg hr0]
  induction k generalizing r with
  | zero => simpa [momentPrefix, nestedKernel] using weighted_geometric_hasSum hr
  | succ k ih =>
    have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / 6 := by positivity
    have hkl : ((k + 1 : ℕ) : ℝ) / 6 < 1 := by
      have : ((k + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hk
      linarith
    let A : ℕ → ℝ := fun n => weight n * r ^ n * momentPrefix k n
    have hweight (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity
    have hA (n : ℕ) : 0 ≤ A n :=
      mul_nonneg (mul_nonneg (hweight n) (pow_nonneg hr0 n)) (momentPrefix_nonneg k n)
    have hAsum : Summable A := by
      apply Summable.of_nonneg_of_le hA _ (weighted_geometric_summable hr)
      intro n
      exact (mul_le_mul_of_nonneg_left (momentPrefix_le_one (by omega : k ≤ 5) n)
        (mul_nonneg (hweight n) (pow_nonneg hr0 n))).trans_eq (mul_one _)
    have hsum := hasSum_betaAverage hkp hkl A hA hAsum
    have hval : betaAverage (((k + 1 : ℕ) : ℝ) / 6)
        (fun x => ∑' n : ℕ, A n * x ^ n) = nestedKernel (k + 1) r := by
      change betaAverage _ _ = betaAverage _ _
      apply betaAverage_congr_Ioo
      intro x hx
      have hrx0 : 0 ≤ r * x := mul_nonneg hr0 hx.1.le
      have hrx1 : r * x < 1 :=
        ((mul_le_mul_of_nonneg_left hx.2.le hr0).trans_eq (mul_one r)).trans_lt hr1
      have hh := ih (by omega : k ≤ 5) hrx0 hrx1
        (by rwa [abs_of_nonneg hrx0])
      rw [← hh.tsum_eq]
      apply tsum_congr
      intro n
      dsimp [A]
      rw [mul_pow]
      ring
    rw [hval] at hsum
    apply hsum.congr_fun
    intro n
    dsimp [A]
    rw [momentPrefix_succ]
    ring

theorem coefficient_eq_momentPrefix (n : ℕ) :
    coefficient n = rho ^ n * momentPrefix 5 n := by
  have hprod : momentPrefix 5 n = risingProduct n / (Nat.factorial n : ℝ) ^ 5 := by
    unfold momentPrefix risingProduct
    calc
      (∏ j ∈ Finset.Icc (1 : ℕ) 5, gammaMoment ((j : ℝ) / 6) n) =
          ∏ j ∈ Finset.Icc (1 : ℕ) 5,
            (ascPochhammer ℝ n).eval ((j : ℝ) / 6) / (Nat.factorial n : ℝ) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
        exact gammaMoment_eq_ascPochhammer (by linarith) n
      _ = (∏ j ∈ Finset.Icc (1 : ℕ) 5, (ascPochhammer ℝ n).eval ((j : ℝ) / 6)) /
          (Nat.factorial n : ℝ) ^ 5 := by
        rw [Finset.prod_div_distrib]
        norm_num
  rw [coefficient_eq_risingProduct, hprod]
  ring

theorem term_hasSum_integral : HasSum term (nestedKernel 5 rho) := by
  have h := nestedKernel_hasSum 5 (by omega) (r := rho)
    (by norm_num [rho]) (by norm_num [rho])
  apply h.congr_fun
  intro n
  rw [term_eq_coefficient_mul_weight, coefficient_eq_momentPrefix]
  ring

theorem term_tsum_integral : (∑' n : ℕ, term n) = nestedKernel 5 rho :=
  term_hasSum_integral.tsum_eq

end Row12
