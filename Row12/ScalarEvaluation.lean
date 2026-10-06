import Row12.EscapeApplication
import Row12.BetaLowerEndpoint
import Row12.OuterEndpointApplication
import Row12EulerSupport.UpperEndpoint

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

theorem betaFluxBalanced_upperEndpoint :
    Tendsto betaFluxBalanced (nhdsWithin (1:ℝ) (Iio 1)) (nhds (0:ℂ)) := by
  have he : betaFluxBalanced = Row12EulerSupport.betaBalanced := by
    funext U
    unfold betaFluxBalanced betaFluxCircle Row12EulerSupport.betaBalanced
    rw [smul_eq_mul]
    rfl
  rw [he]
  exact Row12EulerSupport.betaBalanced_tendsto

theorem scalarTotalFlux_lowerEndpoint :
    Tendsto scalarTotalFlux (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds (1/(36*Real.pi^2))) := by
  change Tendsto (fun U : ℝ => (betaFluxBalanced U+outerPrimitiveFlux (U:ℂ)).re)
    (nhdsWithin 0 (Ioi 0)) (nhds (1/(36*Real.pi^2)))
  have hh := betaFluxBalanced_lowerEndpoint.add
    (outer_primitive_flux_tendsto_zero.mono_left nhdsWithin_le_nhds)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa only [Function.comp_def,scalarTotalFlux,add_zero,Complex.ofReal_re] using hr

theorem scalarTotalFlux_upperEndpoint :
    Tendsto scalarTotalFlux (nhdsWithin (1:ℝ) (Iio 1)) (nhds 0) := by
  change Tendsto (fun U : ℝ => (betaFluxBalanced U+outerPrimitiveFlux (U:ℂ)).re)
    (nhdsWithin 1 (Iio 1)) (nhds 0)
  have hh := betaFluxBalanced_upperEndpoint.add outer_primitive_flux_upperEndpoint
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa only [Function.comp_def,scalarTotalFlux,zero_add,Complex.zero_re] using hr

theorem scalar_uniform_integral_value :
    (∫ U : ℝ in 0..1, scalarIntegrand U)=375/(4*Real.pi^2) := by
  obtain ⟨L,hL⟩ := scalarTotalFlux_escape_limit
  have hleftlim : Tendsto scalarTotalFlux (nhdsWithin escapePoint (Iio escapePoint)) (nhds L) :=
    hL.mono_left (nhdsWithin_mono _ (fun U hU => by
      simp only [mem_compl_iff,mem_singleton_iff]
      exact ne_of_lt hU))
  have hrightlim : Tendsto scalarTotalFlux (nhdsWithin escapePoint (Ioi escapePoint)) (nhds L) :=
    hL.mono_left (nhdsWithin_mono _ (fun U hU => by
      simp only [mem_compl_iff,mem_singleton_iff]
      exact ne_of_gt hU))
  have hint : IntervalIntegrable (fun U : ℝ => -scalarIntegrand U/3375) volume 0 1 :=
    scalarIntegrand_intervalIntegrable.neg.div_const 3375
  have hintL : IntervalIntegrable (fun U : ℝ => -scalarIntegrand U/3375)
      volume 0 escapePoint := hint.mono_set (by
    rw [uIcc_of_le escapePoint_mem.1.le,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl escapePoint_mem.2.le)
  have hintR : IntervalIntegrable (fun U : ℝ => -scalarIntegrand U/3375)
      volume escapePoint 1 := hint.mono_set (by
    rw [uIcc_of_le escapePoint_mem.2.le,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc escapePoint_mem.1.le le_rfl)
  have hleft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    escapePoint_mem.1 (fun U hU => scalarTotalFlux_hasDerivAt hU.1
      (hU.2.trans escapePoint_mem.2)
      (scalar_escape_factor_ne_zero hU.1 hU.2.ne)) hintL
    scalarTotalFlux_lowerEndpoint hleftlim
  have hright := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    escapePoint_mem.2 (fun U hU => scalarTotalFlux_hasDerivAt
      (escapePoint_mem.1.trans hU.1) hU.2
      (scalar_escape_factor_ne_zero (escapePoint_mem.1.trans hU.1) hU.1.ne')) hintR
    hrightlim scalarTotalFlux_upperEndpoint
  have hsum := intervalIntegral.integral_add_adjacent_intervals hintL hintR
  rw [hleft,hright] at hsum
  rw [intervalIntegral.integral_div,intervalIntegral.integral_neg] at hsum
  have hpi : Real.pi^2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  field_simp [hpi] at hsum ⊢
  nlinarith [hsum]

theorem row12_hasSum :
    HasSum (fun n : ℕ =>
      (Nat.factorial (6*n):ℝ)/(Nat.factorial n:ℝ)^6 *
        (532*(n:ℝ)^2+126*(n:ℝ)+9)/(10:ℝ)^(6*n))
      (375/(4*Real.pi^2)) := by
  have hh := term_hasSum_uniformIntegral
  change HasSum term (∫ U : ℝ in 0..1, scalarIntegrand U) at hh
  rw [scalar_uniform_integral_value] at hh
  exact hh

theorem row12_summable :
    Summable (fun n : ℕ =>
      (Nat.factorial (6*n):ℝ)/(Nat.factorial n:ℝ)^6 *
        (532*(n:ℝ)^2+126*(n:ℝ)+9)/(10:ℝ)^(6*n)) :=
  term_summable

theorem row12_tsum :
    (∑' n : ℕ, (Nat.factorial (6*n):ℝ)/(Nat.factorial n:ℝ)^6 *
      (532*(n:ℝ)^2+126*(n:ℝ)+9)/(10:ℝ)^(6*n)) =
      375/(4*Real.pi^2) := row12_hasSum.tsum_eq

end Row12

#print axioms Row12.betaFluxBalanced_upperEndpoint
#print axioms Row12.scalarTotalFlux_lowerEndpoint
#print axioms Row12.scalarTotalFlux_upperEndpoint
#print axioms Row12.scalar_uniform_integral_value
#print axioms Row12.row12_hasSum
#print axioms Row12.row12_summable
#print axioms Row12.row12_tsum
