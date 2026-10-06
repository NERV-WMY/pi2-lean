import Row12.BetaLowerGeometry
import Row12.FixedInnerEndpoint

open Set Filter Metric Complex
open scoped Topology

namespace Row12

theorem beta_lower_deformation_eventually :
    betaFluxBalanced =ᶠ[nhdsWithin 0 (Ioi 0)] (fun U : ℝ =>
      betaFluxCircle (U:ℂ) (1/10)+
        betaBranchNumerator (scalarBetaPositiveResidue U) (scalarLambda (scalarPathX U))
          (scalarPolePlus U)) := by
  have hLC : ContinuousAt (fun U : ℝ => (scalarLambda (scalarPathX U):ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp scalarLambda_path_continuous.continuousAt
  have hL0 : ‖(scalarLambda (scalarPathX 0):ℂ)‖ < (1/10:ℝ) := by
    norm_num [scalarLambda,scalarPathX,rho,norm_div]
  have hL : ∀ᶠ U in nhds (0:ℝ), ‖(scalarLambda (scalarPathX U):ℂ)‖ < (1/10:ℝ) :=
    (continuous_norm.continuousAt.comp
      (f := fun U : ℝ => (scalarLambda (scalarPathX U):ℂ)) (x := 0) hLC).tendsto.eventually
        (Iio_mem_nhds hL0)
  have hA0 : (1/10:ℝ) < scalarPolePlus 0 := by rw [scalar_contact_poles.1]; norm_num
  have hA : ∀ᶠ U in nhds (0:ℝ), (1/10:ℝ) < scalarPolePlus U :=
    scalarPolePlus_continuous.continuousAt.tendsto.eventually (Ioi_mem_nhds hA0)
  have hRC : Continuous (fun U : ℝ => Real.sqrt (scalarLambda (scalarPathX U))) :=
    Real.continuous_sqrt.comp scalarLambda_path_continuous
  have hR0 : Real.sqrt (scalarLambda (scalarPathX 0)) < 1 := by
    norm_num [scalarLambda,scalarPathX,rho]
  have hR : ∀ᶠ U in nhds (0:ℝ), Real.sqrt (scalarLambda (scalarPathX U)) < 1 :=
    hRC.continuousAt.tendsto.eventually (Iio_mem_nhds hR0)
  have hDC : ContinuousAt (fun U : ℝ => betaFrameDenom (scalarPathX U:ℂ)) 0 := by
    unfold betaFrameDenom betaFrameM scalarPathX
    fun_prop
  have hD0 : betaFrameDenom (scalarPathX 0:ℂ) ≠ 0 := by
    norm_num [betaFrameDenom,betaFrameM,scalarPathX]
  have hD : ∀ᶠ U in nhds (0:ℝ), betaFrameDenom (scalarPathX U:ℂ) ≠ 0 :=
    hDC.tendsto.eventually (eventually_ne_nhds hD0)
  have hU1n : ∀ᶠ U : ℝ in nhds 0, U < 1 :=
    isOpen_Iio.mem_nhds (by norm_num : (0:ℝ) ∈ Iio 1)
  filter_upwards [hL.filter_mono nhdsWithin_le_nhds,hA.filter_mono nhdsWithin_le_nhds,
    hR.filter_mono nhdsWithin_le_nhds,hD.filter_mono nhdsWithin_le_nhds,
    hU1n.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with U hLU hAU hRU hDU hU1 hU0
  have hp := scalarPolePlus_pos_lt_radius hU0 hU1
  have hm := scalarPoleMinus_gt_radius hU0 hU1
  have he := betaFluxCircle_singlePole_deformation hU0 hU1
    (by norm_num : (0:ℝ) < 1/10) hLU hAU hp.2 hm hRU hDU
  change betaFluxBalanced U-betaFluxCircle (U:ℂ) (1/10) = _ at he
  rw [sub_eq_iff_eq_add] at he
  exact he.trans (add_comm _ _)

theorem betaFluxBalanced_lowerEndpoint :
    Tendsto betaFluxBalanced (nhdsWithin 0 (Ioi 0))
      (nhds ((1/(36*Real.pi^2):ℝ):ℂ)) := by
  have hsmall : Tendsto (fun U : ℝ => betaFluxCircle (U:ℂ) (1/10))
      (nhds 0) (nhds 0) := by
    exact fixedInnerFlux_tendsto_zero
  have hmono : nhdsWithin (0:ℝ) (Ioi 0) ≤ nhds 0 := nhdsWithin_le_nhds
  have hh := (hsmall.mono_left hmono).add
    (beta_positive_residue_limit.mono_left hmono)
  simpa only [zero_add] using hh.congr' beta_lower_deformation_eventually.symm

end Row12

#print axioms Row12.beta_lower_deformation_eventually
#print axioms Row12.betaFluxBalanced_lowerEndpoint
