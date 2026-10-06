import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

open Set intervalIntegral
open scoped Interval

namespace Row12EulerSupport

noncomputable def endpointMap (p y : ℝ) : ℝ :=
  (1 - y) / (1 - (1 - p) * y)

noncomputable def derivativeKernel (p x : ℝ) : ℝ :=
  x ^ (5 / 6 : ℝ) * (1 - x) ^ (-5 / 6 : ℝ) *
    (1 - (1 - p) * x) ^ (-7 / 6 : ℝ)

theorem endpointMapDenominator_pos {p y : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 < 1 - (1 - p) * y := by
  have h := mul_le_mul_of_nonneg_left hy.2 (by linarith : 0 ≤ 1 - p)
  nlinarith

theorem endpointMap_mem_Ioo {p y : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) : endpointMap p y ∈ Ioo (0 : ℝ) 1 := by
  have hd := endpointMapDenominator_pos hp hp1 ⟨hy.1.le, hy.2.le⟩
  change 0 < (1 - y) / (1 - (1 - p) * y) ∧
    (1 - y) / (1 - (1 - p) * y) < 1
  constructor
  · exact div_pos (sub_pos.mpr hy.2) hd
  · apply (div_lt_one hd).2
    nlinarith [hy.1]

theorem endpointMap_hasDerivAt {p y : ℝ} (hd : 1 - (1 - p) * y ≠ 0) :
    HasDerivAt (endpointMap p)
      (-p / (1 - (1 - p) * y) ^ 2) y := by
  have h := ((hasDerivAt_id y).const_sub 1).div
    (((hasDerivAt_id y).const_mul (1 - p)).const_sub 1) hd
  have he : (-1 * (1 - (1 - p) * y) - (1 - y) * -((1 - p) * 1)) /
      (1 - (1 - p) * y) ^ 2 = -p / (1 - (1 - p) * y) ^ 2 := by
    congr 1
    ring
  convert! h.congr_deriv he using 1

theorem endpointMap_continuousOn {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ContinuousOn (endpointMap p) (Icc (0 : ℝ) 1) := by
  apply (continuous_const.sub continuous_id).continuousOn.div
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  intro y hy
  exact (endpointMapDenominator_pos hp hp1 hy).ne'

theorem endpointMap_zero {p : ℝ} : endpointMap p 0 = 1 := by
  simp [endpointMap]

theorem endpointMap_one {p : ℝ} : endpointMap p 1 = 0 := by
  simp [endpointMap]

theorem endpointMap_factors {p y : ℝ} (hd : 1 - (1 - p) * y ≠ 0) :
    1 - endpointMap p y = (p / (1 - (1 - p) * y)) * y ∧
    1 - (1 - p) * endpointMap p y = p / (1 - (1 - p) * y) := by
  dsimp only [endpointMap]
  constructor
  · calc
      1 - (1 - y) / (1 - (1 - p) * y) =
          ((1 - (1 - p) * y) - (1 - y)) / (1 - (1 - p) * y) := by
        symm
        rw [sub_div, div_self hd]
      _ = (p / (1 - (1 - p) * y)) * y := by
        rw [show (1 - (1 - p) * y) - (1 - y) = p * y by ring]
        ring
  · calc
      1 - (1 - p) * ((1 - y) / (1 - (1 - p) * y)) =
          ((1 - (1 - p) * y) - (1 - p) * (1 - y)) / (1 - (1 - p) * y) := by
        symm
        rw [sub_div, div_self hd]
        ring
      _ = p / (1 - (1 - p) * y) := by
        congr 1
        ring

theorem derivativeKernel_power_cancel {p y : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    derivativeKernel p (endpointMap p y) *
      (-p / (1 - (1 - p) * y) ^ 2) =
    -(1 / p) * (y ^ (-5 / 6 : ℝ) * endpointMap p y ^ (5 / 6 : ℝ)) := by
  have hd := endpointMapDenominator_pos hp hp1 ⟨hy.1.le, hy.2.le⟩
  let t : ℝ := p / (1 - (1 - p) * y)
  have ht : 0 < t := div_pos hp hd
  have hf := endpointMap_factors hd.ne'
  have htprod : t ^ (-5 / 6 : ℝ) * t ^ (-7 / 6 : ℝ) = t⁻¹ ^ 2 := by
    rw [← Real.rpow_add ht]
    norm_num
  unfold derivativeKernel
  rw [hf.1, hf.2, Real.mul_rpow ht.le hy.1.le]
  change endpointMap p y ^ (5 / 6 : ℝ) *
    (t ^ (-5 / 6 : ℝ) * y ^ (-5 / 6 : ℝ)) * t ^ (-7 / 6 : ℝ) *
      (-p / (1 - (1 - p) * y) ^ 2) = _
  calc
    _ = endpointMap p y ^ (5 / 6 : ℝ) * y ^ (-5 / 6 : ℝ) *
      (t ^ (-5 / 6 : ℝ) * t ^ (-7 / 6 : ℝ)) *
        (-p / (1 - (1 - p) * y) ^ 2) := by ring
    _ = _ := by
      rw [htprod]
      dsimp only [t]
      field_simp [hp.ne', hd.ne']

theorem derivativeKernel_substitution {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    p * (∫ x : ℝ in 0..1, derivativeKernel p x) =
      ∫ y : ℝ in 0..1, y ^ (-5 / 6 : ℝ) * endpointMap p y ^ (5 / 6 : ℝ) := by
  have hs := integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0 : ℝ)) (b := 1)
    (f := endpointMap p) (f' := fun y => -p / (1 - (1 - p) * y) ^ 2)
    (g := derivativeKernel p)
    (by simpa only [uIcc_of_le zero_le_one] using endpointMap_continuousOn hp hp1)
    (by
      intro y hy
      simp only [min_eq_left zero_le_one, max_eq_right zero_le_one] at hy
      exact endpointMap_hasDerivAt (endpointMapDenominator_pos hp hp1 ⟨hy.1.le, hy.2.le⟩).ne')
    (by
      intro y hy
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.le) (sq_nonneg _))
  rw [endpointMap_zero, endpointMap_one] at hs
  rw [integral_symm (0 : ℝ) 1] at hs
  have he : (∫ y : ℝ in 0..1,
      (derivativeKernel p ∘ endpointMap p) y * (-p / (1 - (1 - p) * y) ^ 2)) =
      -(1 / p) * (∫ y : ℝ in 0..1,
        y ^ (-5 / 6 : ℝ) * endpointMap p y ^ (5 / 6 : ℝ)) := by
    rw [← integral_const_mul]
    apply integral_congr_Ioo_of_le zero_le_one
    intro y hy
    exact derivativeKernel_power_cancel hp hp1 hy
  rw [he] at hs
  have hm := congrArg (fun z : ℝ => -p * z) hs
  field_simp [hp.ne'] at hm
  nlinarith [hm]

end Row12EulerSupport

#print axioms Row12EulerSupport.endpointMapDenominator_pos
#print axioms Row12EulerSupport.endpointMap_mem_Ioo
#print axioms Row12EulerSupport.endpointMap_hasDerivAt
#print axioms Row12EulerSupport.endpointMap_continuousOn
#print axioms Row12EulerSupport.endpointMap_zero
#print axioms Row12EulerSupport.endpointMap_one
#print axioms Row12EulerSupport.endpointMap_factors
#print axioms Row12EulerSupport.derivativeKernel_power_cancel
#print axioms Row12EulerSupport.derivativeKernel_substitution
