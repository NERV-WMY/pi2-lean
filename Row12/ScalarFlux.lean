import Row12.BetaBalancedDerivative
import Row12.ScalarLoaded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

noncomputable def scalarTotalFlux (U : ℝ) : ℝ :=
  (betaFluxBalanced U+outerPrimitiveFlux (U:ℂ)).re

theorem scalarTotalFlux_hasDerivAt {U : ℝ} (hU : 0 < U) (hU1 : U < 1)
    (hE : 99*scalarPathX U-50 ≠ 0) :
    HasDerivAt scalarTotalFlux (-scalarIntegrand U/3375) U := by
  have hx := scalarPathX_mem hU hU1
  have hxC : 1-(U:ℂ)^2=(scalarPathX U:ℂ) := (betaFrame_real_path_agreement U).1
  have hx0 : 1-(U:ℂ)^2 ≠ 0 := by
    rw [hxC]
    exact Complex.ofReal_ne_zero.mpr hx.1.ne'
  have hEC : 99*(1-(U:ℂ)^2)-50 ≠ 0 := by
    rw [hxC]
    exact_mod_cast hE
  obtain ⟨_,hr1,hl⟩ := scalar_balanced_circle_domain hU hU1
  have hq : ‖outerPrimitiveLambda (1-(U:ℂ)^2)‖ < 1 := by
    rw [hxC]
    have he : outerPrimitiveLambda (scalarPathX U:ℂ)=(scalarLambda (scalarPathX U):ℂ) := by
      simp [outerPrimitiveLambda,scalarLambda,rho]
    rw [he]
    exact hl.trans hr1
  have ho := (outer_primitive_flux_hasDerivAt (U:ℂ) hx0 hEC hq).comp_ofReal
  rw [hxC] at ho
  have hh := (betaFluxBalanced_hasDerivAt hU hU1 hE).add ho
  have hload : scalarComplexLoaded (outerPrimitiveLambda (scalarPathX U:ℂ)) =
      (scalarIntegrand U:ℂ) := by
    have he : outerPrimitiveLambda (scalarPathX U:ℂ) = ((rho*(1-U^2)^3:ℝ):ℂ) := by
      simp [outerPrimitiveLambda,scalarPathX,rho]
    rw [he]
    exact scalarComplexLoaded_cast (scalarIntegrand_path_bounds ⟨hU.le,hU1.le⟩).1
      (scalarIntegrand_path_bounds ⟨hU.le,hU1.le⟩).2
  have hd := hh.congr_deriv (show
      -dotProduct (outerSourceRow (scalarPathX U:ℂ))
          (sixthNormalState (outerPrimitiveLambda (scalarPathX U:ℂ)))+
        (dotProduct (outerSourceRow (scalarPathX U:ℂ))
          (sixthNormalState (outerPrimitiveLambda (scalarPathX U:ℂ)))-
          scalarComplexLoaded (outerPrimitiveLambda (scalarPathX U:ℂ))/3375) =
        ((-scalarIntegrand U/3375:ℝ):ℂ) by
      rw [hload]
      push_cast
      ring)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt U hd
  change HasDerivAt (fun V : ℝ =>
    (betaFluxBalanced V+outerPrimitiveFlux (V:ℂ)).re) (-scalarIntegrand U/3375) U
  simpa only [Function.comp_def,Pi.add_apply,Complex.reCLM_apply,Complex.ofReal_re] using hr

end Row12

#print axioms Row12.scalarComplexLoaded_cast
#print axioms Row12.scalarIntegrand_path_bounds
#print axioms Row12.scalarComplexLoaded_analyticAt
#print axioms Row12.scalarIntegrand_continuousOn
#print axioms Row12.scalarIntegrand_intervalIntegrable
#print axioms Row12.scalarTotalFlux_hasDerivAt
