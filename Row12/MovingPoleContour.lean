import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

open MeasureTheory Set Metric Complex
open scoped Topology

namespace Row12

theorem singlePole_annulus_integral (F : ℂ → ℂ) (a : ℂ) (r R : ℝ) (V : Set ℂ)
    (hr : 0 < r) (har : r < ‖a‖) (haR : ‖a‖ < R)
    (hV : IsOpen V) (ha : a ∈ V)
    (hsub : closedBall (0:ℂ) R \ ball (0:ℂ) r ⊆ V)
    (hF : DifferentiableOn ℂ F V) :
    (∮ s in C(0,R), F s/(s-a))-(∮ s in C(0,r), F s/(s-a)) =
      (2*Real.pi*Complex.I)*F a := by
  have hrR : r < R := har.trans haR
  have hD : DifferentiableOn ℂ (dslope F a) V :=
    (Complex.differentiableOn_dslope (hV.mem_nhds ha)).2 hF
  have hin (s : ℂ) (hs : s ∈ ball (0:ℂ) R \ closedBall (0:ℂ) r) :
      s ∈ V := hsub ⟨ball_subset_closedBall hs.1,fun he => hs.2 (ball_subset_closedBall he)⟩
  have hsame : (∮ s in C(0,R), dslope F a s) = ∮ s in C(0,r), dslope F a s :=
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR.le
      countable_empty (hD.continuousOn.mono hsub) (by
        intro s hs
        exact hD.differentiableAt (hV.mem_nhds (hin s hs.1)))
  have hne (t : ℝ) (ht : t=r ∨ t=R) (s : ℂ) (hs : s ∈ sphere (0:ℂ) t) : s ≠ a := by
    have hst : ‖s‖=t := by simpa using mem_sphere.mp hs
    intro he
    rw [he] at hst
    rcases ht with rfl | rfl <;> linarith
  have hVS (t : ℝ) (ht : t=r ∨ t=R) : sphere (0:ℂ) t ⊆ V := by
    intro s hs
    have hst : ‖s‖=t := by simpa using mem_sphere.mp hs
    apply hsub
    constructor
    · apply mem_closedBall.mpr
      simpa only [dist_zero_right,hst] using (by rcases ht with rfl | rfl <;> linarith : t ≤ R)
    · intro hb
      have hb' : ‖s‖ < r := by simpa using mem_ball.mp hb
      rcases ht with rfl | rfl <;> linarith
  have hsplit (t : ℝ) (ht : t=r ∨ t=R) (ht0 : 0 ≤ t) :
      (∮ s in C(0,t), F s/(s-a)) =
        (∮ s in C(0,t), dslope F a s)+F a*(∮ s in C(0,t), (s-a)⁻¹) := by
    have hDi : CircleIntegrable (dslope F a) 0 t :=
      (hD.continuousOn.mono (hVS t ht)).circleIntegrable ht0
    have hIi : CircleIntegrable (fun s : ℂ => F a*(s-a)⁻¹) 0 t :=
      ((continuousOn_id.sub continuousOn_const).inv₀ (fun s hs =>
        sub_ne_zero.mpr (hne t ht s hs))).circleIntegrable ht0 |>.const_mul (F a)
    calc
      _ = ∮ s in C(0,t), dslope F a s+F a*(s-a)⁻¹ := by
        apply circleIntegral.integral_congr ht0
        intro s hs
        change F s/(s-a) = dslope F a s+F a*(s-a)⁻¹
        rw [dslope_of_ne F (hne t ht s hs)]
        simp only [slope,vsub_eq_sub,smul_eq_mul]
        field_simp [sub_ne_zero.mpr (hne t ht s hs)]
        ring
      _ = _ := by rw [circleIntegral.integral_add hDi hIi,circleIntegral.integral_const_mul]
  have hsmallne (s : ℂ) (hs : s ∈ closedBall (0:ℂ) r) : s-a ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hh : ‖s‖ ≤ r := by simpa using mem_closedBall.mp hs
    rw [he] at hh
    linarith
  have hsmall : (∮ s in C(0,r), (s-a)⁻¹) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
      ((continuousOn_id.sub continuousOn_const).inv₀ hsmallne) (by
        intro s hs
        exact (differentiableAt_id.sub_const a).inv (hsmallne s (ball_subset_closedBall hs.1)))
  have hlarge : (∮ s in C(0,R), (s-a)⁻¹) = 2*Real.pi*Complex.I :=
    circleIntegral.integral_sub_inv_of_mem_ball (by simpa using haR)
  rw [hsplit R (Or.inr rfl) (hr.trans hrR).le,hsplit r (Or.inl rfl) hr.le,
    hsame,hsmall,hlarge]
  ring

end Row12

#print axioms Row12.singlePole_annulus_integral
