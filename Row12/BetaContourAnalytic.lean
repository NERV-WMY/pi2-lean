import Row12.AngularContour
import Row12.ComplexRealSeries
import Row12.BetaPoleResidue
import Row12.MovingPoleContour

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

noncomputable def betaFluxIntegrand (U s : ℂ) : ℂ :=
  betaPair (scalarBetaSFull U s) (dualState s) (dualState (betaFrameB U s))

noncomputable def betaFluxCircle (U : ℂ) (r : ℝ) : ℂ :=
  (2*Real.pi*I:ℂ)⁻¹*(∮ s in C(0,r), betaFluxIntegrand U s)

noncomputable def betaFluxBalanced (U : ℝ) : ℂ :=
  betaFluxCircle (U:ℂ) (Real.sqrt (scalarLambda (scalarPathX U)))

noncomputable def betaBranchNumerator (B : Matrix (Fin 3) (Fin 3) ℂ)
    (lambda s : ℂ) : ℂ :=
  betaPair B (dualState s) (dualState (lambda/s))

theorem dualState_entry_analyticAt (i : Fin 3) (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (fun z => dualState z i) q := by
  have hM (j : Fin 3) : AnalyticAt ℂ (fun z => dualStateMatrix z j i) q := by
    have hh : DifferentiableOn ℂ (fun z : ℂ => dualStateMatrix z j i) univ := by
      intro z _
      exact (dual_state_matrix_entry_hasDerivAt (𝕜 := ℂ) z j i).differentiableAt.differentiableWithinAt
    exact hh.analyticAt Filter.univ_mem
  unfold dualState Matrix.mulVec dotProduct
  simp only [Matrix.transpose_apply]
  convert! Finset.analyticAt_sum (Finset.univ : Finset (Fin 3))
    (fun j _ => (hM j).mul (nativeState_entry_analyticAt j q hq)) using 1

theorem betaBranchNumerator_analyticAt (B : Matrix (Fin 3) (Fin 3) ℂ)
    (lambda s : ℂ) (hs0 : s ≠ 0) (hs : ‖s‖ < 1) (hb : ‖lambda/s‖ < 1) :
    AnalyticAt ℂ (betaBranchNumerator B lambda) s := by
  have hquot : AnalyticAt ℂ (fun z : ℂ => lambda/z) s :=
    analyticAt_const.div analyticAt_id hs0
  unfold betaBranchNumerator betaPair
  have hi (i : Fin 3) : AnalyticAt ℂ
      (fun z => ∑ j : Fin 3, dualState z i*B i j*dualState (lambda/z) j) s := by
    convert! Finset.analyticAt_sum (Finset.univ : Finset (Fin 3)) (fun j _ =>
      (((dualState_entry_analyticAt i s hs).mul
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => B i j) s)).mul
        ((dualState_entry_analyticAt j (lambda/s) hb).comp hquot))) using 1
  convert! Finset.analyticAt_sum (Finset.univ : Finset (Fin 3)) (fun i _ => hi i) using 1

theorem betaBranchNumerator_differentiableOn (B : Matrix (Fin 3) (Fin 3) ℂ)
    (lambda : ℂ) (V : Set ℂ)
    (hV : ∀ s ∈ V, s ≠ 0 ∧ ‖s‖ < 1 ∧ ‖lambda/s‖ < 1) :
    DifferentiableOn ℂ (betaBranchNumerator B lambda) V := by
  intro s hs
  obtain ⟨hs0,hs1,hb⟩ := hV s hs
  exact (betaBranchNumerator_analyticAt B lambda s hs0 hs1 hb).differentiableAt.differentiableWithinAt

theorem betaFluxIntegrand_partialFractions {U : ℝ} (hU : 0 < U) (hU1 : U < 1) (s : ℂ)
    (hd : betaFrameDenom (scalarPathX U:ℂ) ≠ 0)
    (hsa : s-(scalarPolePlus U:ℂ) ≠ 0) (hsb : s-(scalarPoleMinus U:ℂ) ≠ 0) :
    betaFluxIntegrand (U:ℂ) s =
      betaBranchNumerator (scalarBetaPositiveResidue U) (scalarLambda (scalarPathX U)) s /
        (s-(scalarPolePlus U:ℂ))+
      betaBranchNumerator (scalarBetaNegativeResidue U) (scalarLambda (scalarPathX U)) s /
        (s-(scalarPoleMinus U:ℂ)) := by
  have hx : betaFrameX (U:ℂ) = (scalarPathX U:ℂ) := by simp [betaFrameX,scalarPathX]
  have hl := (betaFrame_real_agreement (scalarPathX U)).2.2.2.2.2.2
  unfold betaFluxIntegrand
  rw [scalar_beta_partialFractions hU hU1 s hd hsa hsb]
  unfold betaBranchNumerator betaPair betaFrameB
  rw [hx,hl]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,mul_add,add_mul,
    Finset.sum_add_distrib,div_eq_mul_inv,Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  all_goals apply Finset.sum_congr rfl; intro j _; ring

theorem betaBranch_annulus_domain (lambda s : ℂ) {r R : ℝ}
    (hr : 0 < r) (hl : ‖lambda‖ < r) (hR : R < 1)
    (hs : s ∈ closedBall (0:ℂ) R \ ball (0:ℂ) r) :
    s ≠ 0 ∧ ‖s‖ < 1 ∧ ‖lambda/s‖ < 1 := by
  have hsR : ‖s‖ ≤ R := by simpa using mem_closedBall.mp hs.1
  have hsr : r ≤ ‖s‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hs.2
  have hspos : 0 < ‖s‖ := hr.trans_le hsr
  refine ⟨norm_ne_zero_iff.mp hspos.ne',hsR.trans_lt hR,?_⟩
  rw [norm_div]
  exact (div_lt_one hspos).2 (hl.trans_le hsr)

theorem betaBranch_polefree_annulus_integral (B : Matrix (Fin 3) (Fin 3) ℂ)
    (lambda a : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hl : ‖lambda‖ < r) (hR : R < 1)
    (ha : ∀ s ∈ closedBall (0:ℂ) R \ ball (0:ℂ) r, s-a ≠ 0) :
    (∮ s in C(0,R), betaBranchNumerator B lambda s/(s-a)) =
      ∮ s in C(0,r), betaBranchNumerator B lambda s/(s-a) := by
  have hh (s : ℂ) (hs : s ∈ closedBall (0:ℂ) R \ ball (0:ℂ) r) :
      DifferentiableAt ℂ (fun z => betaBranchNumerator B lambda z/(z-a)) s := by
    obtain ⟨hs0,hs1,hb⟩ := betaBranch_annulus_domain lambda s hr hl hR hs
    exact (betaBranchNumerator_analyticAt B lambda s hs0 hs1 hb).differentiableAt.div
      (differentiableAt_id.sub_const a) (ha s hs)
  exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    countable_empty (fun s hs => (hh s hs).continuousAt.continuousWithinAt) (by
      intro s hs
      exact hh s ⟨ball_subset_closedBall hs.1.1,
        fun he => hs.1.2 (ball_subset_closedBall he)⟩)

theorem betaFluxCircle_singlePole_deformation {U : ℝ} (hU : 0 < U) (hU1 : U < 1)
    {r R : ℝ} (hr : 0 < r) (hl : ‖(scalarLambda (scalarPathX U):ℂ)‖ < r)
    (ha : r < scalarPolePlus U) (haR : scalarPolePlus U < R)
    (hbR : R < scalarPoleMinus U) (hR : R < 1)
    (hd : betaFrameDenom (scalarPathX U:ℂ) ≠ 0) :
    betaFluxCircle (U:ℂ) R-betaFluxCircle (U:ℂ) r =
      betaBranchNumerator (scalarBetaPositiveResidue U) (scalarLambda (scalarPathX U))
        (scalarPolePlus U) := by
  let lambda : ℂ := scalarLambda (scalarPathX U)
  let a : ℂ := scalarPolePlus U
  let b : ℂ := scalarPoleMinus U
  let A : Set ℂ := closedBall 0 R \ ball 0 r
  let V : Set ℂ := {s | ‖lambda‖ < ‖s‖ ∧ ‖s‖ < 1}
  let F : ℂ → ℂ := betaBranchNumerator (scalarBetaPositiveResidue U) lambda
  let G : ℂ → ℂ := betaBranchNumerator (scalarBetaNegativeResidue U) lambda
  have hrR : r < R := ha.trans haR
  have ha0 : 0 < scalarPolePlus U := hr.trans ha
  have hb0 : 0 < scalarPoleMinus U := (hr.trans hrR).trans hbR
  have han : ‖a‖ = scalarPolePlus U := Complex.norm_of_nonneg ha0.le
  have hbn : ‖b‖ = scalarPoleMinus U := Complex.norm_of_nonneg hb0.le
  have hV : IsOpen V := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have haV : a ∈ V := ⟨hl.trans (by simpa only [han] using ha),by simpa only [han] using haR.trans hR⟩
  have hAV : A ⊆ V := by
    intro s hs
    have hsR : ‖s‖ ≤ R := by simpa using mem_closedBall.mp hs.1
    have hsr : r ≤ ‖s‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hs.2
    exact ⟨hl.trans_le hsr,hsR.trans_lt hR⟩
  have hVD (s : ℂ) (hs : s ∈ V) : s ≠ 0 ∧ ‖s‖ < 1 ∧ ‖lambda/s‖ < 1 := by
    have hspos : 0 < ‖s‖ := (norm_nonneg lambda).trans_lt hs.1
    refine ⟨norm_ne_zero_iff.mp hspos.ne',hs.2,?_⟩
    rw [norm_div]
    exact (div_lt_one hspos).2 hs.1
  have hF : DifferentiableOn ℂ F V := betaBranchNumerator_differentiableOn _ lambda V hVD
  have hG : DifferentiableOn ℂ G V := betaBranchNumerator_differentiableOn _ lambda V hVD
  have hsmallpole (s : ℂ) (hs : s ∈ A) : s-b ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hsR : ‖s‖ ≤ R := by simpa using mem_closedBall.mp hs.1
    rw [he,hbn] at hsR
    linarith
  have hGat (s : ℂ) (hs : s ∈ A) :
      DifferentiableAt ℂ (fun z => G z/(z-b)) s :=
    (hG.differentiableAt (hV.mem_nhds (hAV hs))).div
      (differentiableAt_id.sub_const b) (hsmallpole s hs)
  have hGeq : (∮ s in C(0,R), G s/(s-b)) = ∮ s in C(0,r), G s/(s-b) :=
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR.le
      countable_empty (fun s hs => (hGat s hs).continuousAt.continuousWithinAt) (by
        intro s hs
        exact hGat s ⟨ball_subset_closedBall hs.1.1,
          fun he => hs.1.2 (ball_subset_closedBall he)⟩)
  have hFeq := singlePole_annulus_integral F a r R V hr
    (by simpa only [han] using ha) (by simpa only [han] using haR) hV haV hAV hF
  have hsplit (t : ℝ) (ht : t=r ∨ t=R) (ht0 : 0 ≤ t) :
      (∮ s in C(0,t), betaFluxIntegrand (U:ℂ) s) =
        (∮ s in C(0,t), F s/(s-a))+(∮ s in C(0,t), G s/(s-b)) := by
    have hSA (s : ℂ) (hs : s ∈ sphere 0 t) : s ∈ A := by
      have hst : ‖s‖=t := by simpa using mem_sphere.mp hs
      constructor
      · apply mem_closedBall.mpr
        simpa only [dist_zero_right,hst] using (by rcases ht with rfl | rfl <;> linarith : t ≤ R)
      · intro hh
        have hh' : ‖s‖ < r := by simpa using mem_ball.mp hh
        rcases ht with rfl | rfl <;> linarith
    have hsa (s : ℂ) (hs : s ∈ sphere 0 t) : s-a ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      have hst : ‖s‖=t := by simpa using mem_sphere.mp hs
      rw [he,han] at hst
      rcases ht with rfl | rfl <;> linarith
    have hFi : CircleIntegrable (fun s => F s/(s-a)) 0 t :=
      ((hF.continuousOn.mono (fun s hs => hAV (hSA s hs))).div
        (continuousOn_id.sub continuousOn_const) hsa).circleIntegrable ht0
    have hGi : CircleIntegrable (fun s => G s/(s-b)) 0 t :=
      ((hG.continuousOn.mono (fun s hs => hAV (hSA s hs))).div
        (continuousOn_id.sub continuousOn_const) (fun s hs => hsmallpole s (hSA s hs))).circleIntegrable ht0
    calc
      _ = ∮ s in C(0,t), F s/(s-a)+G s/(s-b) := by
        apply circleIntegral.integral_congr ht0
        intro s hs
        exact betaFluxIntegrand_partialFractions hU hU1 s hd (hsa s hs) (hsmallpole s (hSA s hs))
      _ = _ := circleIntegral.integral_add hFi hGi
  have htau : (2*Real.pi*I:ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  unfold betaFluxCircle
  rw [hsplit R (Or.inr rfl) (hr.trans hrR).le,hsplit r (Or.inl rfl) hr.le,hGeq]
  calc
    _ = (2*Real.pi*I:ℂ)⁻¹*
        ((∮ s in C(0,R), F s/(s-a))-(∮ s in C(0,r), F s/(s-a))) := by ring
    _ = F a := by rw [hFeq]; field_simp [htau]

end Row12

#print axioms Row12.dualState_entry_analyticAt
#print axioms Row12.betaBranchNumerator_analyticAt
#print axioms Row12.betaBranchNumerator_differentiableOn
#print axioms Row12.betaFluxIntegrand_partialFractions
#print axioms Row12.betaBranch_annulus_domain
#print axioms Row12.betaBranch_polefree_annulus_integral
#print axioms Row12.betaFluxCircle_singlePole_deformation
