import Row12.BetaContourAnalytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

attribute [local fun_prop] analyticAt_fst analyticAt_snd

theorem betaFluxIntegrand_joint_analyticAt (p : ℂ × ℂ)
    (hH : betaFrameH p.1 p.2 ≠ 0) (hs0 : p.2 ≠ 0)
    (hs : ‖p.2‖ < 1) (hb : ‖betaFrameB p.1 p.2‖ < 1) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => betaFluxIntegrand q.1 q.2) p := by
  have hB : AnalyticAt ℂ (fun q : ℂ × ℂ => betaFrameB q.1 q.2) p := by
    unfold betaFrameB betaFrameLambda betaFrameX
    fun_prop (disch := assumption)
  have hX (i : Fin 3) : AnalyticAt ℂ (fun q : ℂ × ℂ => dualState q.2 i) p :=
    (dualState_entry_analyticAt i p.2 hs).comp analyticAt_snd
  have hZ (j : Fin 3) : AnalyticAt ℂ
      (fun q : ℂ × ℂ => dualState (betaFrameB q.1 q.2) j) p :=
    (dualState_entry_analyticAt j (betaFrameB p.1 p.2) hb).comp
      (f := fun q : ℂ × ℂ => betaFrameB q.1 q.2) (x := p) hB
  have hR (i j : Fin 3) : AnalyticAt ℂ
      (fun q : ℂ × ℂ => scalarBetaSFull q.1 q.2 i j) p := by
    change AnalyticAt ℂ (fun q : ℂ × ℂ => q.1*
      ((2*betaFrameLP (betaFrameX q.1) i j*(q.2-betaFrameMid (betaFrameX q.1))+
        2*betaFrameEll (betaFrameX q.1)*betaFrameM (betaFrameX q.1)*
          betaFrameRP (betaFrameX q.1) i j)/betaFrameH q.1 q.2)) p
    apply analyticAt_fst.mul
    apply AnalyticAt.div
    · fin_cases i <;> fin_cases j <;>
        simp [betaFrameLP,betaFrameRP,betaFrameX,betaFrameMid,betaFrameEll,betaFrameM] <;>
        fun_prop
    · unfold betaFrameH betaFrameX betaFrameDenom betaFrameM betaFrameF betaFrameMid betaFrameLambda
      fun_prop
    · exact hH
  unfold betaFluxIntegrand betaPair
  exact Finset.analyticAt_fun_sum _ (fun i _ => Finset.analyticAt_fun_sum _ (fun j _ =>
    ((hX i).mul (hR i j)).mul (hZ j)))

noncomputable def betaFluxParameterValue (U s : ℂ) : ℂ :=
  (fderiv ℂ (fun p : ℂ × ℂ => betaFluxIntegrand p.1 p.2) (U,s)) (1,0)

theorem betaFluxIntegrand_parameter_hasDerivAt (U s : ℂ)
    (hH : betaFrameH U s ≠ 0) (hs0 : s ≠ 0)
    (hs : ‖s‖ < 1) (hb : ‖betaFrameB U s‖ < 1) :
    HasDerivAt (fun V => betaFluxIntegrand V s) (betaFluxParameterValue U s) U := by
  have ha := betaFluxIntegrand_joint_analyticAt (U,s) hH hs0 hs hb
  have hh := (ha.differentiableAt.hasFDerivAt.comp U (hasFDerivAt_prodMk_left U s)).hasDerivAt
  convert! hh using 1

theorem betaFluxParameterValue_joint_continuousAt (p : ℂ × ℂ)
    (hH : betaFrameH p.1 p.2 ≠ 0) (hs0 : p.2 ≠ 0)
    (hs : ‖p.2‖ < 1) (hb : ‖betaFrameB p.1 p.2‖ < 1) :
    ContinuousAt (fun q : ℂ × ℂ => betaFluxParameterValue q.1 q.2) p := by
  have ha := betaFluxIntegrand_joint_analyticAt p hH hs0 hs hb
  exact ha.fderiv.continuousAt.clm_apply continuousAt_const

end Row12

#print axioms Row12.betaFluxIntegrand_joint_analyticAt
#print axioms Row12.betaFluxIntegrand_parameter_hasDerivAt
#print axioms Row12.betaFluxParameterValue_joint_continuousAt
