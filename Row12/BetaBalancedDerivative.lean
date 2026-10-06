import Row12.BetaContourDerivative
import Row12.BetaBalancedGeometry

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

theorem betaFluxBalanced_hasDerivAt {U : ℝ} (hU : 0 < U) (hU1 : U < 1)
    (hE : 99*scalarPathX U-50 ≠ 0) :
    HasDerivAt betaFluxBalanced
      (-dotProduct (outerSourceRow (scalarPathX U:ℂ))
        (sixthNormalState (outerPrimitiveLambda (scalarPathX U:ℂ)))) U := by
  obtain ⟨hr,hr1,hl⟩ := scalar_balanced_circle_domain hU hU1
  have hx := scalarPathX_mem hU hU1
  have hd := betaFrameDenom_real_path_ne_zero hU hU1 hE
  have hH := betaFlux_circle_regular hU hU1
    (scalarPolePlus_pos_lt_radius hU hU1).2 (scalarPoleMinus_gt_radius hU hU1) hd
  have hl0 : betaFrameLambda (betaFrameX (U:ℂ)) ≠ 0 := by
    rw [(betaFrame_real_path_agreement U).2]
    exact Complex.ofReal_ne_zero.mpr (scalarLambda_pos hx.1).ne'
  have hh := (betaFluxCircle_hasDerivAt (U:ℂ) hr hr1
    (by simpa only [(betaFrame_real_path_agreement U).2] using hl) hl0 hH).comp_ofReal
  have hx0 : (scalarPathX U:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
  have hx25 : 9*(scalarPathX U:ℂ)-25 ≠ 0 := by
    have hM : betaFrameM (scalarPathX U:ℂ) ≠ 0 := by
      rw [(betaFrame_real_agreement (scalarPathX U)).2.2.1]
      exact Complex.ofReal_ne_zero.mpr (scalarM_pos hx.2).ne'
    intro h
    apply hM
    unfold betaFrameM
    linear_combination -h
  have hx50 : 99*(scalarPathX U:ℂ)-50 ≠ 0 := by exact_mod_cast hE
  have hLo : outerPrimitiveLambda (scalarPathX U:ℂ)=
      betaFrameLambda (betaFrameX (U:ℂ)) := by
    rw [(betaFrame_real_path_agreement U).1]
    rfl
  have hlouter : ‖outerPrimitiveLambda (scalarPathX U:ℂ)‖<
      Real.sqrt (scalarLambda (scalarPathX U)) := by
    rw [hLo,(betaFrame_real_path_agreement U).2]
    exact hl
  rw [(betaFrame_real_path_agreement U).1,angular_source_integral_eq_outer
    (scalarPathX U:ℂ) hx0 hx25 hx50 hr hr1 hlouter] at hh
  exact hh.congr_of_eventuallyEq (beta_balanced_fixedCircle_eventually hU hU1 hE)

end Row12

#print axioms Row12.betaFluxCircle_hasDerivAt
#print axioms Row12.beta_balanced_fixedCircle_eventually
#print axioms Row12.angular_source_integral_eq_outer
#print axioms Row12.betaFluxBalanced_hasDerivAt
