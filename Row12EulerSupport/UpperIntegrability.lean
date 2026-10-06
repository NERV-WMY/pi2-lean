import Row12.BetaFrame
import Row12EulerSupport.UpperPoleBound
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Set Metric

namespace Row12EulerSupport

private theorem upperIntegrability_pathX_complex (U : ℝ) :
    Row12.betaFrameX (U : ℂ) = (Row12.scalarPathX U : ℂ) := by
  simp [Row12.betaFrameX, Row12.scalarPathX]

/-- The actual balanced beta integrand is integrable on the shrinking upper-end circle. -/
theorem upperBeta_circleIntegrable {U : ℝ} (hU0 : 0 < U) (hU1 : U < 1)
    (hxsmall : Row12.scalarPathX U ≤ 1 / 100) :
    CircleIntegrable
      (fun s => Row12.betaPair (Row12.scalarBetaSFull (U : ℂ) s)
        (Row12.dualState s) (Row12.dualState (Row12.betaFrameB (U : ℂ) s)))
      0 (Real.sqrt (Row12.scalarLambda (Row12.scalarPathX U))) := by
  let x := Row12.scalarPathX U
  let r := Real.sqrt (Row12.scalarLambda x)
  have hx := Row12.scalarPathX_mem hU0 hU1
  have hr : 0 < r := Real.sqrt_pos.2 (Row12.scalarLambda_pos hx.1)
  have hr1 : r < 1 := (upper_radius_le_quarter hx.1 hxsmall).trans_lt (by linarith)
  apply ContinuousOn.circleIntegrable hr.le
  intro s hs
  have hsr : ‖s‖ = r := by simpa using mem_sphere.mp hs
  have hs0 : s ≠ 0 := upper_circle_nonzero hx.1 hsr
  have hbr : ‖Row12.betaFrameB (U : ℂ) s‖ = r := by
    unfold Row12.betaFrameB
    rw [upperIntegrability_pathX_complex]
    exact upper_balanced_argument_norm hx.1 hsr
  have hb0 : Row12.betaFrameB (U : ℂ) s ≠ 0 :=
    norm_pos_iff.mp (hbr.symm ▸ hr)
  have hd := upper_betaFrame_denominator_nonzero hx.1 hxsmall hsr
  have hv := Row12.dual_state_hasDerivAt s (by rw [hsr]; exact hr1) hs0
  have hw := (Row12.dual_state_hasDerivAt (Row12.betaFrameB (U : ℂ) s)
    (by rw [hbr]; exact hr1) hb0).scomp s (Row12.betaFrameB_hasDerivAt_s (U : ℂ) s hs0)
  have hB (i j : Fin 3) :
      DifferentiableAt ℂ (fun z => Row12.scalarBetaSFull (U : ℂ) z i j) s := by
    simp only [Row12.scalarBetaSFull, Matrix.smul_apply, smul_eq_mul,
      Row12.scalarBetaS, Row12.scalarBetaSChart]
    apply DifferentiableAt.mul
    · fun_prop
    · apply DifferentiableAt.div
      · fun_prop
      · unfold Row12.betaFrameF
        fun_prop
      · simpa only [upperIntegrability_pathX_complex] using hd
  have hf : DifferentiableAt ℂ
      (fun z => Row12.betaPair (Row12.scalarBetaSFull (U : ℂ) z)
        (Row12.dualState z) (Row12.dualState (Row12.betaFrameB (U : ℂ) z))) s := by
    unfold Row12.betaPair
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.fun_sum
    intro j _
    exact (((hasDerivAt_pi.1 hv i).differentiableAt.mul (hB i j)).mul
      (hasDerivAt_pi.1 hw j).differentiableAt)
  exact hf.continuousAt.continuousWithinAt

end Row12EulerSupport

#print axioms Row12EulerSupport.upperBeta_circleIntegrable
