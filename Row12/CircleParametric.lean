import Row12.Hadamard
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Bounded

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

theorem circleParametric_hasDerivAt
    (F F' : ℂ → ℂ → ℂ) (a c : ℂ) (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hF : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2)
      (closedBall a ε ×ˢ sphere c r))
    (hF' : ContinuousOn (fun p : ℂ × ℂ => F' p.1 p.2)
      (closedBall a ε ×ˢ sphere c r))
    (hd : ∀ z ∈ closedBall a ε, ∀ s ∈ sphere c r,
      HasDerivAt (fun q => F q s) (F' z s) z) :
    HasDerivAt (fun z => ∮ s in C(c,r), F z s)
      (∮ s in C(c,r), F' a s) a := by
  have hac : a ∈ closedBall a ε := mem_closedBall_self hε.le
  have hs : closedBall a ε ∈ nhds a := closedBall_mem_nhds a hε
  have hFi (z : ℂ) (hz : z ∈ closedBall a ε) : CircleIntegrable (F z) c r := by
    have hh : ContinuousOn (F z) (sphere c r) :=
      hF.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨hz,hs⟩)
    exact hh.circleIntegrable hr
  have hF'i : CircleIntegrable (F' a) c r := by
    have hh : ContinuousOn (F' a) (sphere c r) :=
      hF'.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨hac,hs⟩)
    exact hh.circleIntegrable hr
  obtain ⟨B,hB⟩ := ((isCompact_closedBall a ε).prod (isCompact_sphere c r)).exists_bound_of_continuousOn hF'
  let J : ℂ → ℝ → ℂ := fun z θ => deriv (circleMap c r) θ * F z (circleMap c r θ)
  let J' : ℂ → ℝ → ℂ := fun z θ => deriv (circleMap c r) θ * F' z (circleMap c r θ)
  have hpi : (0:ℝ) ≤ 2*Real.pi := by positivity
  have hJI (z : ℂ) (hz : z ∈ closedBall a ε) :
      Integrable (J z) (volume.restrict (Ioc 0 (2*Real.pi))) := by
    have hh := (hFi z hz).out.1
    simpa only [J, smul_eq_mul, IntegrableOn] using hh
  have hJ'm : AEStronglyMeasurable (J' a) (volume.restrict (Ioc 0 (2*Real.pi))) := by
    simpa only [J', smul_eq_mul] using hF'i.out.aestronglyMeasurable
  have hbound : ∀ᵐ θ ∂volume.restrict (Ioc 0 (2*Real.pi)),
      ∀ z ∈ closedBall a ε, ‖J' z θ‖ ≤ r*B := by
    exact Filter.Eventually.of_forall (fun θ z hz => by
      dsimp only [J']
      rw [norm_mul]
      have he : ‖deriv (circleMap c r) θ‖ = r := by
        simp [deriv_circleMap, norm_circleMap_zero, abs_of_nonneg hr]
      rw [he]
      exact mul_le_mul_of_nonneg_left (hB (z,circleMap c r θ)
        ⟨hz,circleMap_mem_sphere c hr θ⟩) hr)
  have hconst : Integrable (fun _ : ℝ => r*B)
      (volume.restrict (Ioc 0 (2*Real.pi))) := intervalIntegrable_const.1
  have hdiff : ∀ᵐ θ ∂volume.restrict (Ioc 0 (2*Real.pi)),
      ∀ z ∈ closedBall a ε, HasDerivAt (fun q => J q θ) (J' z θ) z := by
    exact Filter.Eventually.of_forall (fun θ z hz =>
      (hd z hz (circleMap c r θ) (circleMap_mem_sphere c hr θ)).const_mul
        (deriv (circleMap c r) θ))
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (by filter_upwards [hs] with z hz; exact (hJI z hz).aestronglyMeasurable)
    (hJI a hac) hJ'm hbound hconst hdiff).2
  simpa only [circleIntegral, smul_eq_mul, intervalIntegral.integral_of_le hpi, J,J'] using hh

theorem circleIntegral_exactDerivative (P P' : ℂ → ℂ) {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hP : ∀ s ∈ sphere c r, HasDerivAt P (P' s) s) :
    (∮ s in C(c,r), P' s) = 0 := by
  exact circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr
    (fun s hs => (hP s hs).hasDerivWithinAt)

end Row12

#print axioms Row12.circleParametric_hasDerivAt
#print axioms Row12.circleIntegral_exactDerivative
