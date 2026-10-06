import Row12.BetaFrame
import Mathlib.Topology.Order.Compact

open Set

namespace Row12EulerSupport

private noncomputable def upperMidFactor (x : ℂ) : ℂ :=
  27 * (80 - 99 * x + 27 * x ^ 2) / 1000

private noncomputable def upperEllMFactor (x : ℂ) : ℂ :=
  (27 * (9 * x - 16) / 1000) * Row12.betaFrameM x

private theorem upperMid_factor (x : ℂ) :
    Row12.betaFrameMid x = x * upperMidFactor x := by
  unfold Row12.betaFrameMid upperMidFactor
  ring

private theorem upperEllM_factor (x : ℂ) :
    Row12.betaFrameEll x * Row12.betaFrameM x = x * upperEllMFactor x := by
  unfold Row12.betaFrameEll upperEllMFactor
  ring

private theorem upperLP_continuous : Continuous Row12.betaFrameLP := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_iff_continuousAt.mpr fun x =>
    (Row12.betaFrameLP_differentiableAt x i j).continuousAt

private theorem upperRP_continuous : Continuous Row12.betaFrameRP := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_iff_continuousAt.mpr fun x =>
    (Row12.betaFrameRP_differentiableAt x i j).continuousAt

private theorem upper_polynomial_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, x ∈ Icc (0 : ℝ) 1 →
      (∀ i j : Fin 3, ‖Row12.betaFrameLP (x : ℂ) i j‖ ≤ C ∧
        ‖Row12.betaFrameRP (x : ℂ) i j‖ ≤ C) ∧
      ‖upperMidFactor (x : ℂ)‖ ≤ C ∧ ‖upperEllMFactor (x : ℂ)‖ ≤ C := by
  have hL : Continuous (fun x : ℝ => ‖fun i j : Fin 3 => Row12.betaFrameLP (x : ℂ) i j‖) := by
    apply Continuous.norm
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply j).comp ((continuous_apply i).comp
      (upperLP_continuous.comp Complex.continuous_ofReal))
  have hR : Continuous (fun x : ℝ => ‖fun i j : Fin 3 => Row12.betaFrameRP (x : ℂ) i j‖) := by
    apply Continuous.norm
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply j).comp ((continuous_apply i).comp
      (upperRP_continuous.comp Complex.continuous_ofReal))
  have hM : Continuous (fun x : ℝ => ‖upperMidFactor (x : ℂ)‖) := by
    unfold upperMidFactor
    fun_prop
  have hE : Continuous (fun x : ℝ => ‖upperEllMFactor (x : ℂ)‖) := by
    unfold upperEllMFactor Row12.betaFrameM
    fun_prop
  have hcompact : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  obtain ⟨a, ha⟩ := hcompact.bddAbove_image hL.continuousOn
  obtain ⟨b, hb⟩ := hcompact.bddAbove_image hR.continuousOn
  obtain ⟨c, hc⟩ := hcompact.bddAbove_image hM.continuousOn
  obtain ⟨d, hd⟩ := hcompact.bddAbove_image hE.continuousOn
  let C : ℝ := |a| + |b| + |c| + |d| + 1
  have haC : a ≤ C := by
    dsimp [C]
    linarith [le_abs_self a, abs_nonneg b, abs_nonneg c, abs_nonneg d]
  have hbC : b ≤ C := by
    dsimp [C]
    linarith [le_abs_self b, abs_nonneg a, abs_nonneg c, abs_nonneg d]
  have hcC : c ≤ C := by
    dsimp [C]
    linarith [le_abs_self c, abs_nonneg a, abs_nonneg b, abs_nonneg d]
  have hdC : d ≤ C := by
    dsimp [C]
    linarith [le_abs_self d, abs_nonneg a, abs_nonneg b, abs_nonneg c]
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d]
  · intro x hx
    refine ⟨?_, (hc (mem_image_of_mem _ hx)).trans hcC,
      (hd (mem_image_of_mem _ hx)).trans hdC⟩
    intro i j
    constructor
    · exact (norm_le_pi_norm (fun j : Fin 3 => Row12.betaFrameLP (x : ℂ) i j) j).trans
        ((norm_le_pi_norm (fun i j : Fin 3 => Row12.betaFrameLP (x : ℂ) i j) i).trans
          ((ha (mem_image_of_mem _ hx)).trans haC))
    · exact (norm_le_pi_norm (fun j : Fin 3 => Row12.betaFrameRP (x : ℂ) i j) j).trans
        ((norm_le_pi_norm (fun i j : Fin 3 => Row12.betaFrameRP (x : ℂ) i j) i).trans
          ((hb (mem_image_of_mem _ hx)).trans hbC))

theorem upperBetaNumerator_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ∀ s : ℂ, ‖s‖ ≤ x → ∀ i j : Fin 3,
      ‖2 * Row12.betaFrameLP (x : ℂ) i j * (s - Row12.betaFrameMid (x : ℂ)) +
        2 * Row12.betaFrameEll (x : ℂ) * Row12.betaFrameM (x : ℂ) *
          Row12.betaFrameRP (x : ℂ) i j‖ ≤ K * x := by
  obtain ⟨C, hC1, hC⟩ := upper_polynomial_bounds
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  refine ⟨2 * C * (1 + C) + 2 * C * C, by nlinarith, ?_⟩
  intro x hx0 hx1 s hs i j
  obtain ⟨hLR, hMid, hEll⟩ := hC x ⟨hx0, hx1⟩
  have hMid' : ‖Row12.betaFrameMid (x : ℂ)‖ ≤ C * x := by
    rw [upperMid_factor, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hMid hx0
  have hEll' : ‖Row12.betaFrameEll (x : ℂ) * Row12.betaFrameM (x : ℂ)‖ ≤ C * x := by
    rw [upperEllM_factor, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hEll hx0
  have hsub : ‖s - Row12.betaFrameMid (x : ℂ)‖ ≤ (1 + C) * x := by
    calc
      ‖s - Row12.betaFrameMid (x : ℂ)‖ ≤ ‖s‖ + ‖Row12.betaFrameMid (x : ℂ)‖ := norm_sub_le _ _
      _ ≤ x + C * x := add_le_add hs hMid'
      _ = (1 + C) * x := by ring
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    norm_num
  calc
    ‖2 * Row12.betaFrameLP (x : ℂ) i j * (s - Row12.betaFrameMid (x : ℂ)) +
        2 * Row12.betaFrameEll (x : ℂ) * Row12.betaFrameM (x : ℂ) *
          Row12.betaFrameRP (x : ℂ) i j‖ ≤
        ‖2 * Row12.betaFrameLP (x : ℂ) i j * (s - Row12.betaFrameMid (x : ℂ))‖ +
          ‖2 * Row12.betaFrameEll (x : ℂ) * Row12.betaFrameM (x : ℂ) *
            Row12.betaFrameRP (x : ℂ) i j‖ := norm_add_le _ _
    _ = 2 * ‖Row12.betaFrameLP (x : ℂ) i j‖ * ‖s - Row12.betaFrameMid (x : ℂ)‖ +
        2 * ‖Row12.betaFrameEll (x : ℂ) * Row12.betaFrameM (x : ℂ)‖ *
          ‖Row12.betaFrameRP (x : ℂ) i j‖ := by
      rw [show 2 * Row12.betaFrameEll (x : ℂ) * Row12.betaFrameM (x : ℂ) =
        2 * (Row12.betaFrameEll (x : ℂ) * Row12.betaFrameM (x : ℂ)) by ring]
      simp only [norm_mul, htwo]
    _ ≤ 2 * C * ((1 + C) * x) + 2 * (C * x) * C := by
      apply add_le_add
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hLR i j).1 (by norm_num)
        · exact hsub
        · exact norm_nonneg _
        · positivity
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hEll' (by norm_num)
        · exact (hLR i j).2
        · exact norm_nonneg _
        · positivity
    _ = (2 * C * (1 + C) + 2 * C * C) * x := by ring

theorem upperBetaFullNumerator_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ U : ℝ, 0 ≤ U → U ≤ 1 →
      ∀ s : ℂ, ‖s‖ ≤ 1 - U ^ 2 → ∀ i j : Fin 3,
      ‖(U : ℂ) *
        (2 * Row12.betaFrameLP ((1 - U ^ 2 : ℝ) : ℂ) i j *
            (s - Row12.betaFrameMid ((1 - U ^ 2 : ℝ) : ℂ)) +
          2 * Row12.betaFrameEll ((1 - U ^ 2 : ℝ) : ℂ) *
            Row12.betaFrameM ((1 - U ^ 2 : ℝ) : ℂ) *
            Row12.betaFrameRP ((1 - U ^ 2 : ℝ) : ℂ) i j)‖ ≤ K * (1 - U ^ 2) := by
  obtain ⟨K, hK, hbound⟩ := upperBetaNumerator_bound
  refine ⟨K, hK, ?_⟩
  intro U hU0 hU1 s hs i j
  have hx0 : 0 ≤ 1 - U ^ 2 := by nlinarith
  have hx1 : 1 - U ^ 2 ≤ 1 := by nlinarith [sq_nonneg U]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hU0]
  calc
    U * ‖2 * Row12.betaFrameLP ((1 - U ^ 2 : ℝ) : ℂ) i j *
          (s - Row12.betaFrameMid ((1 - U ^ 2 : ℝ) : ℂ)) +
        2 * Row12.betaFrameEll ((1 - U ^ 2 : ℝ) : ℂ) *
          Row12.betaFrameM ((1 - U ^ 2 : ℝ) : ℂ) *
          Row12.betaFrameRP ((1 - U ^ 2 : ℝ) : ℂ) i j‖ ≤
        1 * ‖2 * Row12.betaFrameLP ((1 - U ^ 2 : ℝ) : ℂ) i j *
          (s - Row12.betaFrameMid ((1 - U ^ 2 : ℝ) : ℂ)) +
        2 * Row12.betaFrameEll ((1 - U ^ 2 : ℝ) : ℂ) *
          Row12.betaFrameM ((1 - U ^ 2 : ℝ) : ℂ) *
          Row12.betaFrameRP ((1 - U ^ 2 : ℝ) : ℂ) i j‖ :=
      mul_le_mul_of_nonneg_right hU1 (norm_nonneg _)
    _ ≤ K * (1 - U ^ 2) := by simpa only [one_mul] using hbound (1 - U ^ 2) hx0 hx1 s hs i j

end Row12EulerSupport

#print axioms Row12EulerSupport.upperBetaNumerator_bound
#print axioms Row12EulerSupport.upperBetaFullNumerator_bound
