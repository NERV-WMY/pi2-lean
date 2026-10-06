import Row12.BetaFrame
import Row12EulerSupport.UpperNativeBound
import Row12EulerSupport.UpperPoleBound
import Row12EulerSupport.UpperMatrixBound
import Row12EulerSupport.UpperIntegrability
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Set Filter Metric Complex
open scoped Topology

namespace Row12EulerSupport

noncomputable def betaBalanced (U : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ s in C(0, Real.sqrt (Row12.scalarLambda (Row12.scalarPathX U))),
      Row12.betaPair (Row12.scalarBetaSFull (U : ℂ) s)
        (Row12.dualState s) (Row12.dualState (Row12.betaFrameB (U : ℂ) s))

theorem upperPathX_complex (U : ℝ) :
    Row12.betaFrameX (U : ℂ) = (Row12.scalarPathX U : ℂ) := by
  simp [Row12.betaFrameX, Row12.scalarPathX]

theorem upperBetaB_agreement (U : ℝ) (s : ℂ) :
    Row12.betaFrameB (U : ℂ) s = (Row12.scalarLambda (Row12.scalarPathX U) : ℂ) / s := by
  unfold Row12.betaFrameB
  rw [upperPathX_complex]
  simp [Row12.betaFrameLambda, Row12.betaFrameRho, Row12.scalarLambda, Row12.rho]

theorem betaBalanced_formula (U : ℝ) :
    betaBalanced U = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ s in C(0, Real.sqrt (Row12.scalarLambda (1 - U ^ 2))),
        Row12.betaPair (Row12.scalarBetaSFull (U : ℂ) s)
          (Row12.dualState s)
          (Row12.dualState ((Row12.scalarLambda (1 - U ^ 2) : ℂ) / s)) := by
  unfold betaBalanced
  simp only [upperBetaB_agreement, Row12.scalarPathX]

theorem upperNormalizedCircle_norm_le {f : ℂ → ℂ} {r M : ℝ} (hr : 0 ≤ r)
    (hf : ∀ s ∈ sphere (0 : ℂ) r, ‖f s‖ ≤ M) :
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ s in C(0, r), f s‖ ≤ r * M := by
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [norm_smul, hc]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * r * M) :=
      mul_le_mul_of_nonneg_left
        (circleIntegral.norm_integral_le_of_norm_le_const hr hf) (by positivity)
    _ = r * M := by field_simp [Real.pi_ne_zero]

theorem upperBetaPair_norm_le {B : Matrix (Fin 3) (Fin 3) ℂ}
    {v w : Fin 3 → ℂ} {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hv : ∀ i, ‖v i‖ ≤ A) (hw : ∀ j, ‖w j‖ ≤ A)
    (hB : ∀ i j, ‖B i j‖ ≤ L) :
    ‖Row12.betaPair B v w‖ ≤ 9 * (A * L * A) := by
  unfold Row12.betaPair
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖v i * B i j * w j‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, A * L * A := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hv i) (hB i j) (norm_nonneg _) hA)
        (hw j) (norm_nonneg _) (mul_nonneg hA hL)
    _ = _ := by simp; ring

theorem betaBalanced_circleIntegrable {U : ℝ} (hU0 : 0 < U) (hU1 : U < 1)
    (hxsmall : Row12.scalarPathX U ≤ 1 / 100) :
    CircleIntegrable
      (fun s => Row12.betaPair (Row12.scalarBetaSFull (U : ℂ) s)
        (Row12.dualState s) (Row12.dualState (Row12.betaFrameB (U : ℂ) s)))
      0 (Real.sqrt (Row12.scalarLambda (Row12.scalarPathX U))) := by
  exact upperBeta_circleIntegrable hU0 hU1 hxsmall

theorem upperRadius_cancel {x : ℝ} (hx : 0 < x) (C K : ℝ) :
    let r := Real.sqrt (Row12.scalarLambda x)
    r * (9 * ((C * r ^ 2) * ((K * x) / (x ^ 5 * r)) * (C * r ^ 2))) =
      (9 * C ^ 2 * K * Row12.rho ^ 2) * x ^ 2 := by
  dsimp only
  let r := Real.sqrt (Row12.scalarLambda x)
  have hr : 0 < r := Real.sqrt_pos.2 (Row12.scalarLambda_pos hx)
  have hs : r ^ 2 = Row12.rho * x ^ 3 :=
    Real.sq_sqrt (Row12.scalarLambda_pos hx).le
  change r * (9 * ((C * r ^ 2) * ((K * x) / (x ^ 5 * r)) * (C * r ^ 2))) = _
  calc
    _ = 9 * C ^ 2 * K * r ^ 4 / x ^ 4 := by
      field_simp [hx.ne', hr.ne']
    _ = _ := by
      rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hs]
      field_simp [hx.ne']

theorem betaBalanced_quadratic_bound :
    ∃ M > 0, ∃ η > 0, ∀ U : ℝ, 0 < U → U < 1 →
      Row12.scalarPathX U ≤ η → ‖betaBalanced U‖ ≤ M * (Row12.scalarPathX U) ^ 2 := by
  obtain ⟨K, hK, hN⟩ := upperBetaFullNumerator_bound
  obtain ⟨C, hC, δ, hδ, hδhalf, hV⟩ := upperDualState_quadratic_bound
  have hρ : 0 < Row12.rho := by norm_num [Row12.rho]
  refine ⟨9 * C ^ 2 * K * Row12.rho ^ 2, by positivity,
    min (1 / 100) δ, lt_min (by norm_num) hδ, ?_⟩
  intro U hU0 hU1 hsmall
  let x := Row12.scalarPathX U
  let r := Real.sqrt (Row12.scalarLambda x)
  have hx : 0 < x ∧ x < 1 := Row12.scalarPathX_mem hU0 hU1
  have hxsmall : x ≤ 1 / 100 := hsmall.trans (min_le_left _ _)
  have hxδ : x ≤ δ := hsmall.trans (min_le_right _ _)
  have hr : 0 < r := Real.sqrt_pos.2 (Row12.scalarLambda_pos hx.1)
  have hrx : r ≤ x := (upper_radius_le_quarter hx.1 hxsmall).trans (by linarith)
  have hrδ : r ≤ δ := hrx.trans hxδ
  let f : ℂ → ℂ := fun s =>
    Row12.betaPair (Row12.scalarBetaSFull (U : ℂ) s)
      (Row12.dualState s) (Row12.dualState (Row12.betaFrameB (U : ℂ) s))
  have hpair : ∀ s ∈ sphere (0 : ℂ) r,
      ‖f s‖ ≤ 9 * ((C * r ^ 2) * ((K * x) / (x ^ 5 * r)) * (C * r ^ 2)) := by
    intro s hs
    have hsr : ‖s‖ = r := by simpa using mem_sphere.mp hs
    have hbr : ‖Row12.betaFrameB (U : ℂ) s‖ = r := by
      unfold Row12.betaFrameB
      rw [upperPathX_complex]
      exact upper_balanced_argument_norm hx.1 hsr
    have hDstrong := upper_betaFrame_denominator_lower hx.1 hxsmall hsr
    have hDpos : 0 < x ^ 5 * r := mul_pos (pow_pos hx.1 5) hr
    have hD : x ^ 5 * r ≤
        ‖Row12.betaFrameDenom (x : ℂ) * Row12.betaFrameF (x : ℂ) s‖ := by
      calc
        _ ≤ 57624 * (x ^ 5 * r) := by nlinarith [hDpos.le]
        _ = 57624 * x ^ 5 * r := by ring
        _ ≤ _ := hDstrong
    have hentry (i j : Fin 3) :
        ‖Row12.scalarBetaSFull (U : ℂ) s i j‖ ≤ (K * x) / (x ^ 5 * r) := by
      have hn := hN U hU0.le hU1.le s
        (by convert! hsr.le.trans hrx using 1) i j
      have he : Row12.scalarBetaSFull (U : ℂ) s i j =
          ((U : ℂ) *
            (2 * Row12.betaFrameLP (x : ℂ) i j * (s - Row12.betaFrameMid (x : ℂ)) +
              2 * Row12.betaFrameEll (x : ℂ) * Row12.betaFrameM (x : ℂ) *
                Row12.betaFrameRP (x : ℂ) i j)) /
              (Row12.betaFrameDenom (x : ℂ) * Row12.betaFrameF (x : ℂ) s) := by
        simp only [Row12.scalarBetaSFull, Matrix.smul_apply, smul_eq_mul,
          Row12.scalarBetaS, Row12.scalarBetaSChart, upperPathX_complex]
        ring
      rw [he, norm_div]
      calc
        _ ≤ (K * x) /
            ‖Row12.betaFrameDenom (x : ℂ) * Row12.betaFrameF (x : ℂ) s‖ :=
          div_le_div_of_nonneg_right hn (norm_nonneg _)
        _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hK.le hx.1.le) hDpos hD
    exact upperBetaPair_norm_le (mul_nonneg hC.le (sq_nonneg r))
      (div_nonneg (mul_nonneg hK.le hx.1.le) hDpos.le)
      (fun i => by simpa only [hsr] using hV s (by rw [hsr]; exact hrδ) i)
      (fun j => by
        have hj := hV (Row12.betaFrameB (U : ℂ) s) (by rw [hbr]; exact hrδ) j
        convert! hj using 1
        rw [hbr]) hentry
  have hn := upperNormalizedCircle_norm_le hr.le hpair
  change ‖betaBalanced U‖ ≤ r *
    (9 * ((C * r ^ 2) * ((K * x) / (x ^ 5 * r)) * (C * r ^ 2))) at hn
  exact hn.trans_eq (upperRadius_cancel hx.1 C K)

theorem betaBalanced_tendsto :
    Tendsto betaBalanced (𝓝[Iio 1] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
  obtain ⟨M, hM, η, hη, hbound⟩ := betaBalanced_quadratic_bound
  have hi : Tendsto (fun U : ℝ => U) (𝓝[Iio 1] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hx : Tendsto Row12.scalarPathX (𝓝[Iio 1] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun U : ℝ => 1 - U ^ 2) (𝓝[Iio 1] (1 : ℝ))
        (𝓝 (1 - (1 : ℝ) ^ 2)) := tendsto_const_nhds.sub (hi.pow 2)
    convert! h using 1
    norm_num
  have hU0 : ∀ᶠ U : ℝ in 𝓝[Iio 1] (1 : ℝ), 0 < U :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hU1 : ∀ᶠ U : ℝ in 𝓝[Iio 1] (1 : ℝ), U < 1 := self_mem_nhdsWithin
  have hsmall : ∀ᶠ U : ℝ in 𝓝[Iio 1] (1 : ℝ), Row12.scalarPathX U < η :=
    hx.eventually (Iio_mem_nhds hη)
  have hupper : ∀ᶠ U : ℝ in 𝓝[Iio 1] (1 : ℝ),
      ‖betaBalanced U‖ ≤ M * (Row12.scalarPathX U) ^ 2 := by
    filter_upwards [hU0, hU1, hsmall] with U h0 h1 hs
    exact hbound U h0 h1 hs.le
  have hlim : Tendsto (fun U : ℝ => M * (Row12.scalarPathX U) ^ 2)
      (𝓝[Iio 1] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (hx.pow 2).const_mul M
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Filter.Eventually.of_forall (fun U => norm_nonneg (betaBalanced U))) hupper hlim)

end Row12EulerSupport

#print axioms Row12EulerSupport.upperPathX_complex
#print axioms Row12EulerSupport.upperBetaB_agreement
#print axioms Row12EulerSupport.betaBalanced_formula
#print axioms Row12EulerSupport.upperNormalizedCircle_norm_le
#print axioms Row12EulerSupport.upperBetaPair_norm_le
#print axioms Row12EulerSupport.betaBalanced_circleIntegrable
#print axioms Row12EulerSupport.upperRadius_cancel
#print axioms Row12EulerSupport.betaBalanced_quadratic_bound
#print axioms Row12EulerSupport.betaBalanced_tendsto
