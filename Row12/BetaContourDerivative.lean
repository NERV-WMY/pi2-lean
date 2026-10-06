import Row12.BetaJointAnalytic
import Row12.BetaSourceComparison
import Row12.AngularSourceIntegral
import Row12.FixedInnerEndpoint
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

theorem betaFlux_regular_tube (U : ℂ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖betaFrameLambda (betaFrameX U)‖ < r)
    (hH : ∀ s ∈ sphere (0:ℂ) r, betaFrameH U s ≠ 0) :
    ∃ ε > 0, ∀ V ∈ closedBall U ε, ∀ s ∈ sphere (0:ℂ) r,
      betaFrameH V s ≠ 0 ∧ s ≠ 0 ∧ ‖s‖ < 1 ∧ ‖betaFrameB V s‖ < 1 := by
  have hev : ∀ᶠ V in nhds U, ∀ s ∈ sphere (0:ℂ) r,
      betaFrameH V s ≠ 0 ∧ s ≠ 0 ∧ ‖s‖ < 1 ∧ ‖betaFrameB V s‖ < 1 := by
    apply (isCompact_sphere (0:ℂ) r).eventually_forall_of_forall_eventually
    intro s hs
    obtain ⟨hs0,_,_,hs1,hb⟩ := angular_circle_domain hr hr1 hl hs
    have hhc : ContinuousAt (fun p : ℂ × ℂ => betaFrameH p.1 p.2) (U,s) :=
      fixedInner_H_continuous.continuousAt
    have hhn := hhc.eventually_ne (hH s hs)
    have hs0n : ∀ᶠ p : ℂ × ℂ in nhds (U,s), p.2 ≠ 0 :=
      continuousAt_snd.eventually_ne hs0
    have hs1n : ∀ᶠ p : ℂ × ℂ in nhds (U,s), ‖p.2‖ < 1 :=
      continuousAt_snd.norm.eventually (Iio_mem_nhds hs1)
    have hbn : ∀ᶠ p : ℂ × ℂ in nhds (U,s), ‖betaFrameB p.1 p.2‖ < 1 :=
      (fixedInner_B_continuousAt (U,s) hs0).norm.eventually (Iio_mem_nhds hb)
    filter_upwards [hhn,hs0n,hs1n,hbn] with p hpH hps0 hps1 hpb
    exact ⟨hpH,hps0,hps1,hpb⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ/2,by positivity,?_⟩
  intro V hV s hs
  exact hball (mem_ball.mpr ((mem_closedBall.mp hV).trans_lt (by linarith))) s hs

theorem betaFluxCircle_hasDerivAt (U : ℂ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖betaFrameLambda (betaFrameX U)‖ < r)
    (hl0 : betaFrameLambda (betaFrameX U) ≠ 0)
    (hH : ∀ s ∈ sphere (0:ℂ) r, betaFrameH U s ≠ 0) :
    HasDerivAt (fun V => betaFluxCircle V r)
      (-angularSourceIntegral (betaFrameX U) r) U := by
  obtain ⟨ε,hε,hreg⟩ := betaFlux_regular_tube U hr hr1 hl hH
  let K : Set (ℂ × ℂ) := closedBall U ε ×ˢ sphere (0:ℂ) r
  have hF : ContinuousOn (fun p : ℂ × ℂ => betaFluxIntegrand p.1 p.2) K := by
    intro p hp
    obtain ⟨hHp,hs0,hs,hb⟩ := hreg p.1 hp.1 p.2 hp.2
    exact (betaFluxIntegrand_joint_analyticAt p hHp hs0 hs hb).continuousAt.continuousWithinAt
  have hF' : ContinuousOn (fun p : ℂ × ℂ => betaFluxParameterValue p.1 p.2) K := by
    intro p hp
    obtain ⟨hHp,hs0,hs,hb⟩ := hreg p.1 hp.1 p.2 hp.2
    exact (betaFluxParameterValue_joint_continuousAt p hHp hs0 hs hb).continuousWithinAt
  have hraw := circleParametric_hasDerivAt betaFluxIntegrand betaFluxParameterValue
    U 0 r ε hr.le hε hF hF' (by
      intro V hV s hs
      obtain ⟨hHV,hs0,hsn,hb⟩ := hreg V hV s hs
      exact betaFluxIntegrand_parameter_hasDerivAt V s hHV hs0 hsn hb)
  have hd : betaFrameDenom (betaFrameX U) ≠ 0 := by
    have hsr : (r:ℂ) ∈ sphere (0:ℂ) r := by
      simp only [mem_sphere,dist_zero_right,Complex.norm_of_nonneg hr.le]
    exact (mul_ne_zero_iff.1 (hH r hsr)).1
  have hx0 : betaFrameX U ≠ 0 := by intro h; simp [betaFrameDenom,h] at hd
  have hx25 : 9*betaFrameX U-25 ≠ 0 := by
    intro h
    have hM : betaFrameM (betaFrameX U)=0 := by
      unfold betaFrameM
      linear_combination -h
    simp [betaFrameDenom,hM] at hd
  have hx50 : 99*betaFrameX U-50 ≠ 0 := by intro h; simp [betaFrameDenom,h] at hd
  let P : ℂ → ℂ := fun s => betaPair (scalarBetaU U s) (dualState s) (dualState (betaFrameB U s))
  have hP (s : ℂ) (hs : s ∈ sphere (0:ℂ) r) : HasDerivAt P (deriv P s) s := by
    obtain ⟨hs0,_,_,hsn,hb⟩ := angular_circle_domain hr hr1 hl hs
    exact (scalarBetaU_pair_hasDerivAt_s U s (hH s hs) hsn hs0 hb
      (div_ne_zero hl0 hs0)).differentiableAt.hasDerivAt
  have hPzero := circleIntegral_exactDerivative P (deriv P) hr.le hP
  have hid (s : ℂ) (hs : s ∈ sphere (0:ℂ) r) :
      angularSourceIntegrand (betaFrameX U) s =
        -betaFluxParameterValue U s+deriv P s := by
    obtain ⟨hs0,_,hsl,hsn,hb⟩ := angular_circle_domain hr hr1 hl hs
    have hh := angularSource_actual_beta_derivatives U s (hH s hs) hsn hs0 hsl hb
      (div_ne_zero hl0 hs0)
    change angularSourceIntegrand (betaFrameX U) s =
      -deriv (fun V => betaFluxIntegrand V s) U+deriv P s at hh
    rw [(betaFluxIntegrand_parameter_hasDerivAt U s (hH s hs) hs0 hsn hb).deriv] at hh
    exact hh
  have hDi : CircleIntegrable (betaFluxParameterValue U) 0 r := by
    exact (hF'.comp (continuousOn_const.prodMk continuousOn_id)
      (fun s hs => ⟨mem_closedBall_self hε.le,hs⟩)).circleIntegrable hr.le
  have hSi := angular_source_circleIntegrable (betaFrameX U) hx0 hx25 hx50 hr hr1 hl
  have hPi : CircleIntegrable (deriv P) 0 r := by
    apply (circleIntegrable_congr (by
      intro s hs
      have hsp : s ∈ sphere (0:ℂ) r := by simpa only [abs_of_nonneg hr.le] using hs
      have he := hid s hsp
      change angularSourceIntegrand (betaFrameX U) s+betaFluxParameterValue U s = deriv P s
      rw [he]
      ring)).1
    exact hSi.add hDi
  have hneg : (∮ s in C(0,r), -betaFluxParameterValue U s) =
      -(∮ s in C(0,r), betaFluxParameterValue U s) := by
    simp only [circleIntegral,smul_neg,intervalIntegral.integral_neg]
  have hi : (∮ s in C(0,r), angularSourceIntegrand (betaFrameX U) s) =
      -(∮ s in C(0,r), betaFluxParameterValue U s) := by
    calc
      _ = ∮ s in C(0,r), -betaFluxParameterValue U s+deriv P s :=
        circleIntegral.integral_congr hr.le hid
      _ = (∮ s in C(0,r), -betaFluxParameterValue U s)+
          (∮ s in C(0,r), deriv P s) := by
        simpa only [Pi.neg_apply] using circleIntegral.integral_add hDi.neg hPi
      _ = _ := by
        rw [hneg,hPzero,add_zero]
  apply (hraw.const_mul (2*Real.pi*I:ℂ)⁻¹).congr_deriv
  unfold angularSourceIntegral
  rw [hi]
  ring

end Row12

#print axioms Row12.betaFluxIntegrand_joint_analyticAt
#print axioms Row12.betaFluxIntegrand_parameter_hasDerivAt
#print axioms Row12.betaFluxParameterValue_joint_continuousAt
#print axioms Row12.betaFlux_regular_tube
#print axioms Row12.betaFluxCircle_hasDerivAt
