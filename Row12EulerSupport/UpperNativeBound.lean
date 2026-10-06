import Row12.DualFrame
import Mathlib.Analysis.Analytic.Order

open Filter Asymptotics
open scoped Topology

namespace Row12EulerSupport

theorem upperNativeCoefficient_one : Row12.coefficient3 1 = 5 / 72 := by
  norm_num [Row12.coefficient3]

theorem upperNativeEuler_zero (k : ℕ) :
    Row12.nativeEuler k (0 : ℂ) = (0 : ℂ) ^ k := by
  unfold Row12.nativeEuler
  rw [tsum_eq_single 0]
  · simp [Row12.coefficient3_zero]
  · intro n hn
    simp [zero_pow hn]

theorem upperNativeEuler_deriv_zero (k : ℕ) :
    deriv (Row12.nativeEuler k : ℂ → ℂ) 0 = 5 / 72 := by
  rw [(Row12.nativeEuler_hasDerivAt k (0 : ℂ) (by simp)).deriv]
  calc
    _ = (Row12.coefficient3 1 : ℂ) * (1 : ℂ) ^ (k + 1) *
        (0 : ℂ) ^ ((1 : ℕ) - 1) := by
      rw [tsum_eq_single (1 : ℕ)]
      · norm_num
      · intro n hn
        cases n with
        | zero => simp
        | succ n =>
          cases n with
          | zero => exact (hn rfl).elim
          | succ n => simp
    _ = 5 / 72 := by simp [upperNativeCoefficient_one]

theorem upperNativeEuler_hasDerivAt_zero (k : ℕ) :
    HasDerivAt (Row12.nativeEuler k : ℂ → ℂ) (5 / 72) 0 :=
  (Row12.nativeEuler_hasDerivAt k (0 : ℂ) (by simp)).differentiableAt.hasDerivAt.congr_deriv
    (upperNativeEuler_deriv_zero k)

theorem upperNativeEuler_analyticAt_zero (k : ℕ) :
    AnalyticAt ℂ (Row12.nativeEuler k : ℂ → ℂ) 0 := by
  induction k with
  | zero => exact Row12.nativeF_analyticAt (0 : ℂ) (by simp)
  | succ k ih =>
    have ha : AnalyticAt ℂ (fun q : ℂ => q * deriv (Row12.nativeEuler k) q) 0 := by
      exact analyticAt_id.mul ih.deriv
    apply ha.congr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with q hq
    exact (Row12.nativeEuler_succ_eq k q (by simpa using hq)).symm

theorem upperDualState_zero : (Row12.dualState (0 : ℂ)) = 0 := by
  ext i
  rw [Row12.dual_state_formula]
  fin_cases i <;> simp [upperNativeEuler_zero, Row12.nativeF]

theorem upperDualState_component_hasDerivAt_zero (i : Fin 3) :
    HasDerivAt (fun q : ℂ => Row12.dualState q i) 0 0 := by
  have hid := hasDerivAt_id (0 : ℂ)
  have hone := hasDerivAt_const (0 : ℂ) (1 : ℂ)
  have hF : HasDerivAt (Row12.nativeF : ℂ → ℂ) (5 / 72) 0 := by
    convert! upperNativeEuler_hasDerivAt_zero 0 using 1
  have hE1 := upperNativeEuler_hasDerivAt_zero 1
  have hE2 := upperNativeEuler_hasDerivAt_zero 2
  fin_cases i
  · have h := (((hid.const_mul (-5 / 72 : ℂ)).mul hF).add
      ((hid.const_mul (-1 / 2 : ℂ)).mul hE1)).add ((hone.sub hid).mul hE2)
    convert! h using 1
    · funext q
      simp [Row12.dual_state_formula]
    · simp [Row12.nativeF, upperNativeEuler_zero]
      ring
  · have h := (hid.mul (hid.sub hone)).mul hE1
    convert! h using 1
    · funext q
      simp [Row12.dual_state_formula]
    · simp [upperNativeEuler_zero]
  · have h := (((hid.pow 2).const_mul (2 : ℂ)).mul (hone.sub hid)).mul hF
    convert! h using 1
    · funext q
      simp [Row12.dual_state_formula]
    · simp

theorem upperDualState_hasDerivAt_zero :
    HasDerivAt (Row12.dualState : ℂ → Fin 3 → ℂ) 0 0 := by
  exact hasDerivAt_pi.2 upperDualState_component_hasDerivAt_zero

theorem upperDualState_deriv_zero :
    deriv (Row12.dualState : ℂ → Fin 3 → ℂ) 0 = 0 :=
  upperDualState_hasDerivAt_zero.deriv

theorem upperDualState_analyticAt_zero :
    AnalyticAt ℂ (Row12.dualState : ℂ → Fin 3 → ℂ) 0 := by
  apply AnalyticAt.pi
  intro i
  have hF : AnalyticAt ℂ (Row12.nativeF : ℂ → ℂ) 0 :=
    Row12.nativeF_analyticAt (0 : ℂ) (by simp)
  have hE1 := upperNativeEuler_analyticAt_zero 1
  have hE2 := upperNativeEuler_analyticAt_zero 2
  fin_cases i <;> simp [Row12.dual_state_formula] <;> fun_prop

theorem upperDualState_eventually_quadratic_bound :
    ∃ C > 0, ∀ᶠ q : ℂ in 𝓝 0, ‖Row12.dualState q‖ ≤ C * ‖q‖ ^ 2 := by
  have horder : (2 : ℕ) ≤ analyticOrderAt (Row12.dualState : ℂ → Fin 3 → ℂ) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero upperDualState_analyticAt_zero]
    intro i hi
    interval_cases i
    · simpa only [iteratedDeriv_zero] using upperDualState_zero
    · simpa only [iteratedDeriv_one] using upperDualState_deriv_zero
  obtain ⟨g, hg, hfactor⟩ := (natCast_le_analyticOrderAt upperDualState_analyticAt_zero).1 horder
  have hbound : ∀ᶠ q : ℂ in 𝓝 0, ‖g q‖ < ‖g 0‖ + 1 :=
    hg.continuousAt.norm (gt_mem_nhds (by linarith : ‖g (0 : ℂ)‖ < ‖g 0‖ + 1))
  refine ⟨‖g 0‖ + 1, by positivity, ?_⟩
  filter_upwards [hfactor, hbound] with q hq hnorm
  rw [hq]
  simp only [sub_zero, norm_smul, norm_pow]
  exact (mul_le_mul_of_nonneg_left hnorm.le (sq_nonneg ‖q‖)).trans_eq (mul_comm _ _)

theorem upperDualState_isBigO_sq :
    (Row12.dualState : ℂ → Fin 3 → ℂ) =O[𝓝 0] (fun q : ℂ => ‖q‖ ^ 2) := by
  obtain ⟨C, _, hC⟩ := upperDualState_eventually_quadratic_bound
  apply IsBigO.of_bound C
  filter_upwards [hC] with q hq
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖q‖)] using hq

theorem upperDualState_quadratic_bound :
    ∃ C > 0, ∃ δ > 0, δ ≤ (1 / 2 : ℝ) ∧
      ∀ q : ℂ, ‖q‖ ≤ δ → ∀ i : Fin 3, ‖Row12.dualState q i‖ ≤ C * ‖q‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := upperDualState_eventually_quadratic_bound
  obtain ⟨ε, hε, hεbound⟩ := Metric.eventually_nhds_iff.1 hbound
  refine ⟨C, hC, min (ε / 2) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro q hq i
  apply (norm_le_pi_norm (Row12.dualState q) i).trans
  apply hεbound
  rw [dist_zero_right]
  exact lt_of_le_of_lt (hq.trans (min_le_left _ _)) (by linarith)

end Row12EulerSupport

#print axioms Row12EulerSupport.upperNativeEuler_deriv_zero
#print axioms Row12EulerSupport.upperDualState_zero
#print axioms Row12EulerSupport.upperDualState_hasDerivAt_zero
#print axioms Row12EulerSupport.upperDualState_analyticAt_zero
#print axioms Row12EulerSupport.upperDualState_isBigO_sq
#print axioms Row12EulerSupport.upperDualState_quadratic_bound
