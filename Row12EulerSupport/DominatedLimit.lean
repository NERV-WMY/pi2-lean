import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology Interval

namespace Row12EulerSupport

noncomputable def endpointRatio (p y : ℝ) : ℝ :=
  (1 - y) / (1 - (1 - p) * y)

noncomputable def endpointIntegrand (p y : ℝ) : ℝ :=
  y ^ (-(5 : ℝ) / 6) * endpointRatio p y ^ ((5 : ℝ) / 6)

theorem endpointDenominator_pos {p y : ℝ} (hp : 0 < p) (hy : y ∈ Icc 0 1) :
    0 < 1 - (1 - p) * y := by
  have hpy : 0 ≤ p * y := mul_nonneg hp.le hy.1
  rcases lt_or_eq_of_le hy.2 with hlt | rfl
  · nlinarith
  · simpa using hp

theorem endpointRatio_nonneg {p y : ℝ} (hp : 0 < p) (hy : y ∈ Icc 0 1) :
    0 ≤ endpointRatio p y :=
  div_nonneg (sub_nonneg.mpr hy.2) (endpointDenominator_pos hp hy).le

theorem endpointRatio_le_one {p y : ℝ} (hp : 0 < p) (hy : y ∈ Icc 0 1) :
    endpointRatio p y ≤ 1 := by
  unfold endpointRatio
  apply (div_le_one (endpointDenominator_pos hp hy)).2
  nlinarith [mul_nonneg hp.le hy.1]

theorem endpointRatio_continuousOn {p : ℝ} (hp : 0 < p) :
    ContinuousOn (endpointRatio p) (Icc 0 1) := by
  unfold endpointRatio
  refine (continuousOn_const.sub continuousOn_id).div
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_
  intro y hy
  exact (endpointDenominator_pos hp hy).ne'

theorem endpointIntegrand_nonneg {p y : ℝ} (hp : 0 < p) (hy : y ∈ Icc 0 1) :
    0 ≤ endpointIntegrand p y := by
  exact mul_nonneg (Real.rpow_nonneg hy.1 _)
    (Real.rpow_nonneg (endpointRatio_nonneg hp hy) _)

theorem endpointIntegrand_norm_le {p y : ℝ} (hp : 0 < p) (hy : y ∈ Icc 0 1) :
    ‖endpointIntegrand p y‖ ≤ y ^ (-(5 : ℝ) / 6) := by
  have hpow : endpointRatio p y ^ ((5 : ℝ) / 6) ≤ 1 := by
    simpa using Real.rpow_le_rpow (endpointRatio_nonneg hp hy)
      (endpointRatio_le_one hp hy) (by norm_num : (0 : ℝ) ≤ 5 / 6)
  rw [Real.norm_eq_abs, abs_of_nonneg (endpointIntegrand_nonneg hp hy)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hy.1 _) hpow

theorem endpointBound_intervalIntegrable :
    IntervalIntegrable (fun y : ℝ => y ^ (-(5 : ℝ) / 6)) volume 0 1 := by
  exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)

theorem endpointIntegrand_aestronglyMeasurable {p : ℝ} (hp : 0 < p) :
    AEStronglyMeasurable (endpointIntegrand p) (volume.restrict (Ι (0 : ℝ) 1)) := by
  have hc : ContinuousOn (fun y => endpointRatio p y ^ ((5 : ℝ) / 6)) (Icc 0 1) :=
    (endpointRatio_continuousOn hp).rpow_const (fun _ _ => Or.inr (by norm_num))
  have hsub : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1)
  exact endpointBound_intervalIntegrable.aestronglyMeasurable_restrict_uIoc.mul
    ((hc.mono hsub).aestronglyMeasurable measurableSet_uIoc)

theorem endpointIntegrand_intervalIntegrable {p : ℝ} (hp : 0 < p) :
    IntervalIntegrable (endpointIntegrand p) volume 0 1 := by
  refine endpointBound_intervalIntegrable.mono_fun' (endpointIntegrand_aestronglyMeasurable hp) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
  have hy' : y ∈ Ioc (0 : ℝ) 1 := by
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  exact endpointIntegrand_norm_le hp ⟨hy'.1.le, hy'.2⟩

theorem endpointRatio_tendsto {y : ℝ} (hy : y < 1) :
    Tendsto (fun p : ℝ => endpointRatio p y) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hd : 1 - (1 - (0 : ℝ)) * y ≠ 0 := by nlinarith
  have hp : Tendsto (fun p : ℝ => p) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdlim : Tendsto (fun p : ℝ => 1 - (1 - p) * y) (𝓝[>] (0 : ℝ))
      (𝓝 (1 - (1 - (0 : ℝ)) * y)) :=
    tendsto_const_nhds.sub ((tendsto_const_nhds.sub hp).mul_const y)
  have h : Tendsto (fun p : ℝ => (1 - y) / (1 - (1 - p) * y)) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 - y) / (1 - (1 - (0 : ℝ)) * y))) :=
    tendsto_const_nhds.div hdlim hd
  have hval : (1 - y) / (1 - (1 - (0 : ℝ)) * y) = 1 := by
    simp only [sub_zero, one_mul]
    exact div_self (by linarith : 1 - y ≠ 0)
  simpa only [endpointRatio, hval] using h

theorem endpointIntegrand_tendsto {y : ℝ} (hy : y < 1) :
    Tendsto (fun p : ℝ => endpointIntegrand p y) (𝓝[>] (0 : ℝ))
      (𝓝 (y ^ (-(5 : ℝ) / 6))) := by
  have h : Tendsto (fun p : ℝ => y ^ (-(5 : ℝ) / 6) * endpointRatio p y ^ ((5 : ℝ) / 6))
      (𝓝[>] (0 : ℝ)) (𝓝 (y ^ (-(5 : ℝ) / 6) * (1 : ℝ) ^ ((5 : ℝ) / 6))) :=
    tendsto_const_nhds.mul
      ((endpointRatio_tendsto hy).rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0)))
  simpa only [endpointIntegrand, Real.one_rpow, mul_one] using h

theorem endpointBound_integral :
    (∫ y in (0 : ℝ)..1, y ^ (-(5 : ℝ) / 6)) = 6 := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(5 : ℝ) / 6))]
  norm_num [Real.zero_rpow]

theorem endpointIntegral_tendsto :
    Tendsto (fun p : ℝ => ∫ y in (0 : ℝ)..1, endpointIntegrand p y)
      (𝓝[>] (0 : ℝ)) (𝓝 6) := by
  rw [← endpointBound_integral]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun y : ℝ => y ^ (-(5 : ℝ) / 6))
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact endpointIntegrand_aestronglyMeasurable hp
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact Filter.Eventually.of_forall (fun y hy => by
      have hy' : y ∈ Ioc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
      exact endpointIntegrand_norm_le hp ⟨hy'.1.le, hy'.2⟩)
  · exact endpointBound_intervalIntegrable
  · filter_upwards [volume.ae_ne (1 : ℝ)] with y hyne
    intro hy
    have hy' : y ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
    exact endpointIntegrand_tendsto (lt_of_le_of_ne hy'.2 hyne)

end Row12EulerSupport

#print axioms Row12EulerSupport.endpointRatio_continuousOn
#print axioms Row12EulerSupport.endpointIntegrand_intervalIntegrable
#print axioms Row12EulerSupport.endpointIntegrand_tendsto
#print axioms Row12EulerSupport.endpointBound_integral
#print axioms Row12EulerSupport.endpointIntegral_tendsto
