import Row12.BetaFrame
import Row12.AngularContour
import Mathlib.Topology.UniformSpace.HeineCantor

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

theorem fixedCircleIntegral_tendsto_of_continuousOn
    (F : ℂ → ℂ → ℂ) (a c : ℂ) (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hF : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2)
      (closedBall a ε ×ˢ sphere c r)) :
    Tendsto (fun z => ∮ s in C(c,r), F z s) (𝓝 a)
      (𝓝 (∮ s in C(c,r), F a s)) := by
  have hU : closedBall a ε ∈ 𝓝 a := closedBall_mem_nhds a hε
  have hac : a ∈ closedBall a ε := mem_closedBall_self hε.le
  have hu := ((isCompact_closedBall a ε).prod (isCompact_sphere c r)).uniformContinuousOn_of_continuous hF
  have ht : TendstoUniformlyOn F (F a) (𝓝 a) (sphere c r) := by
    simpa only [nhdsWithin_eq_nhds.2 hU] using hu.tendstoUniformlyOn hac
  apply ht.tendsto_circleIntegral_of_continuousOn hr
  filter_upwards [hU] with z hz
  exact hF.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨hz,hs⟩)

noncomputable def fixedInnerIntegrand (U s : ℂ) : ℂ :=
  betaPair (scalarBetaSFull U s) (dualState s) (dualState (betaFrameB U s))

noncomputable def fixedInnerFlux (U : ℝ) : ℂ :=
  (2*Real.pi*I : ℂ)⁻¹ * ∮ s in C(0,(1/10 : ℝ)), fixedInnerIntegrand (U : ℂ) s

theorem fixedInner_at_zero (s : ℂ) :
    betaFrameH 0 s=38416*(s-27/125)^2 ∧ betaFrameB 0 s=betaFrameRho/s := by
  constructor
  · norm_num only [betaFrameH, betaFrameX, betaFrameDenom, betaFrameM,
      betaFrameF, betaFrameMid, betaFrameLambda, betaFrameRho]
    ring
  · simp [betaFrameB, betaFrameX, betaFrameLambda]

theorem fixedInner_circle_domain (s : ℂ) (hs : s ∈ sphere 0 (1/10 : ℝ)) :
    s ≠ 0 ∧ betaFrameH 0 s ≠ 0 ∧ ‖s‖ < 1 ∧
      ‖betaFrameB 0 s‖=(1458/3125 : ℝ) := by
  have hsn : ‖s‖=(1/10 : ℝ) := by simpa using mem_sphere.mp hs
  have hs0 : s ≠ 0 := norm_ne_zero_iff.mp (by rw [hsn]; norm_num)
  have hsm : s-27/125 ≠ 0 := by
    intro h
    have he : s=(27/125 : ℂ) := sub_eq_zero.mp h
    rw [he] at hsn
    norm_num [norm_div] at hsn
  refine ⟨hs0,?_,by rw [hsn]; norm_num,?_⟩
  · rw [(fixedInner_at_zero s).1]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hsm)
  · rw [(fixedInner_at_zero s).2, norm_div, hsn]
    norm_num [betaFrameRho, norm_div]

theorem fixedInner_H_continuous :
    Continuous (fun p : ℂ × ℂ => betaFrameH p.1 p.2) := by
  unfold betaFrameH betaFrameX betaFrameDenom betaFrameM betaFrameF betaFrameMid betaFrameLambda
  fun_prop

theorem fixedInner_B_continuousAt (p : ℂ × ℂ) (hs0 : p.2 ≠ 0) :
    ContinuousAt (fun q : ℂ × ℂ => betaFrameB q.1 q.2) p := by
  unfold betaFrameB betaFrameLambda betaFrameX
  fun_prop (disch := assumption)

theorem fixedInner_dual_entry_continuousAt (q : ℂ) (hq : ‖q‖ < 1) (i : Fin 3) :
    ContinuousAt (fun z : ℂ => dualState z i) q := by
  change ContinuousAt (fun z : ℂ => ∑ k : Fin 3,
    dualStateMatrix z k i*nativeState z k) q
  exact tendsto_finsetSum _ (fun k _ =>
    (dual_state_matrix_entry_hasDerivAt q k i).continuousAt.mul
      (nativeState_entry_analyticAt k q hq).continuousAt)

theorem fixedInner_beta_entry_continuousAt (p : ℂ × ℂ)
    (hH : betaFrameH p.1 p.2 ≠ 0) (i j : Fin 3) :
    ContinuousAt (fun q : ℂ × ℂ => scalarBetaSFull q.1 q.2 i j) p := by
  change ContinuousAt (fun q : ℂ × ℂ => q.1*
    ((2*betaFrameLP (betaFrameX q.1) i j*(q.2-betaFrameMid (betaFrameX q.1))+
      2*betaFrameEll (betaFrameX q.1)*betaFrameM (betaFrameX q.1)*
        betaFrameRP (betaFrameX q.1) i j)/betaFrameH q.1 q.2)) p
  apply continuousAt_fst.mul
  apply ContinuousAt.div _ fixedInner_H_continuous.continuousAt hH
  fin_cases i <;> fin_cases j <;>
    unfold betaFrameLP betaFrameRP betaFrameX betaFrameMid betaFrameEll betaFrameM <;>
    fun_prop

theorem fixedInner_integrand_continuousAt (p : ℂ × ℂ)
    (hH : betaFrameH p.1 p.2 ≠ 0) (hs0 : p.2 ≠ 0)
    (hs : ‖p.2‖ < 1) (hb : ‖betaFrameB p.1 p.2‖ < 1) :
    ContinuousAt (fun q : ℂ × ℂ => fixedInnerIntegrand q.1 q.2) p := by
  have hX (i : Fin 3) : ContinuousAt (fun q : ℂ × ℂ => dualState q.2 i) p :=
    (fixedInner_dual_entry_continuousAt p.2 hs i).comp continuousAt_snd
  have hZ (i : Fin 3) :
      ContinuousAt (fun q : ℂ × ℂ => dualState (betaFrameB q.1 q.2) i) p :=
    (fixedInner_dual_entry_continuousAt (betaFrameB p.1 p.2) hb i).comp
      (f := fun q : ℂ × ℂ => betaFrameB q.1 q.2) (x := p)
      (fixedInner_B_continuousAt p hs0)
  unfold fixedInnerIntegrand betaPair
  exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
    ((hX i).mul (fixedInner_beta_entry_continuousAt p hH i j)).mul (hZ j)))

theorem fixedInner_regular_tube :
    ∃ ε > 0, ∀ U ∈ closedBall (0 : ℂ) ε, ∀ s ∈ sphere 0 (1/10 : ℝ),
      betaFrameH U s ≠ 0 ∧ s ≠ 0 ∧ ‖s‖ < 1 ∧ ‖betaFrameB U s‖ < 1 := by
  have hev : ∀ᶠ U : ℂ in 𝓝 0, ∀ s ∈ sphere 0 (1/10 : ℝ),
      betaFrameH U s ≠ 0 ∧ s ≠ 0 ∧ ‖s‖ < 1 ∧ ‖betaFrameB U s‖ < 1 := by
    apply (isCompact_sphere (0 : ℂ) (1/10 : ℝ)).eventually_forall_of_forall_eventually
    intro s hs
    obtain ⟨hs0,hH,hsn,hbn⟩ := fixedInner_circle_domain s hs
    have hhc : ContinuousAt (fun p : ℂ × ℂ => betaFrameH p.1 p.2) (0,s) :=
      fixedInner_H_continuous.continuousAt
    have hHn := hhc.eventually_ne hH
    have hsn0 : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,s), p.2 ≠ 0 :=
      continuousAt_snd.eventually_ne hs0
    have hsn1 : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,s), ‖p.2‖ < 1 :=
      continuousAt_snd.norm.eventually (Iio_mem_nhds hsn)
    have hbn1 : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,s), ‖betaFrameB p.1 p.2‖ < 1 :=
      (fixedInner_B_continuousAt (0,s) hs0).norm.eventually
        (Iio_mem_nhds (by change ‖betaFrameB 0 s‖ < 1; rw [hbn]; norm_num))
    filter_upwards [hHn,hsn0,hsn1,hbn1] with p hpH hps0 hps1 hpb1
    exact ⟨hpH,hps0,hps1,hpb1⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ/2,by positivity,?_⟩
  intro U hU s hs
  exact hball (mem_ball.mpr ((mem_closedBall.mp hU).trans_lt (by linarith))) s hs

theorem fixedInner_integrand_zero (s : ℂ) : fixedInnerIntegrand 0 s=0 := by
  simp [fixedInnerIntegrand, scalarBetaSFull, betaPair]

theorem fixedInner_circleIntegral_tendsto_zero :
    Tendsto (fun U : ℂ => ∮ s in C(0,(1/10 : ℝ)), fixedInnerIntegrand U s)
      (𝓝 0) (𝓝 0) := by
  obtain ⟨ε,hε,hreg⟩ := fixedInner_regular_tube
  have hc : ContinuousOn (fun p : ℂ × ℂ => fixedInnerIntegrand p.1 p.2)
      (closedBall 0 ε ×ˢ sphere 0 (1/10 : ℝ)) := by
    intro p hp
    obtain ⟨hH,hs0,hs,hb⟩ := hreg p.1 hp.1 p.2 hp.2
    exact (fixedInner_integrand_continuousAt p hH hs0 hs hb).continuousWithinAt
  have ht := fixedCircleIntegral_tendsto_of_continuousOn fixedInnerIntegrand 0 0
    (1/10) ε (by norm_num) hε hc
  have hz : (∮ s in C(0,(1/10 : ℝ)), fixedInnerIntegrand 0 s)=0 := by
    simp [fixedInner_integrand_zero, circleIntegral]
  rw [hz] at ht
  exact ht

theorem fixedInnerFlux_tendsto_zero : Tendsto fixedInnerFlux (𝓝 0) (𝓝 0) := by
  have ht := fixedInner_circleIntegral_tendsto_zero.comp Complex.continuous_ofReal.continuousAt
  change Tendsto (fun U : ℝ => (2*Real.pi*I : ℂ)⁻¹*
    (∮ s in C(0,(1/10 : ℝ)), fixedInnerIntegrand (U : ℂ) s)) (𝓝 0) (𝓝 0)
  simpa only [Function.comp_apply, mul_zero] using ht.const_mul (2*Real.pi*I : ℂ)⁻¹

end Row12

#print axioms Row12.fixedCircleIntegral_tendsto_of_continuousOn
#print axioms Row12.fixedInner_at_zero
#print axioms Row12.fixedInner_circle_domain
#print axioms Row12.fixedInner_H_continuous
#print axioms Row12.fixedInner_B_continuousAt
#print axioms Row12.fixedInner_dual_entry_continuousAt
#print axioms Row12.fixedInner_beta_entry_continuousAt
#print axioms Row12.fixedInner_integrand_continuousAt
#print axioms Row12.fixedInner_regular_tube
#print axioms Row12.fixedInner_integrand_zero
#print axioms Row12.fixedInner_circleIntegral_tendsto_zero
#print axioms Row12.fixedInnerFlux_tendsto_zero
