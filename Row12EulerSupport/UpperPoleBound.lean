import Row12.BetaFrame

namespace Row12EulerSupport

theorem upper_scalarMid_lower {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 100) :
    x ≤ Row12.scalarMid x := by
  have hq : (1 : ℝ) ≤ 27 * (80 - 99 * x + 27 * x ^ 2) / 1000 := by
    nlinarith [sq_nonneg x]
  calc
    x = x * 1 := by ring
    _ ≤ x * (27 * (80 - 99 * x + 27 * x ^ 2) / 1000) :=
      mul_le_mul_of_nonneg_left hq hx.le
    _ = Row12.scalarMid x := by unfold Row12.scalarMid; ring

theorem upper_radius_le_quarter {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 100) :
    Real.sqrt (Row12.scalarLambda x) ≤ x / 4 := by
  have hx1 : x ≤ 1 := by linarith
  have hc : x ^ 3 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]
  have hl : Row12.scalarLambda x ≤ (x / 4) ^ 2 := by
    unfold Row12.scalarLambda Row12.rho
    nlinarith [sq_nonneg x]
  have hs := Real.sq_sqrt (Row12.scalarLambda_pos hx).le
  have hr := Real.sqrt_nonneg (Row12.scalarLambda x)
  nlinarith

theorem upper_scalarDenom_lower {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 100) :
    57624 * x ^ 4 ≤ Row12.scalarDenom x := by
  have hm : (24 : ℝ) ≤ Row12.scalarM x := by unfold Row12.scalarM; linarith
  have hb : (2401 : ℝ) ≤ (99 * x - 50) ^ 2 := by
    have hh : 99 * x - 50 ≤ -49 := by linarith
    nlinarith
  have hp : (24 : ℝ) * 2401 ≤ Row12.scalarM x * (99 * x - 50) ^ 2 :=
    mul_le_mul hm hb (by norm_num) (by linarith)
  calc
    57624 * x ^ 4 = x ^ 4 * (24 * 2401) := by ring
    _ ≤ x ^ 4 * (Row12.scalarM x * (99 * x - 50) ^ 2) :=
      mul_le_mul_of_nonneg_left hp (pow_nonneg hx.le 4)
    _ = Row12.scalarDenom x := by unfold Row12.scalarDenom; ring

theorem upper_lambda_norm {x : ℝ} (hx : 0 < x) :
    ‖Row12.betaFrameLambda (x : ℂ)‖ = Real.sqrt (Row12.scalarLambda x) ^ 2 := by
  rw [(Row12.betaFrame_real_agreement x).2.2.2.2.2.2, Complex.norm_real,
    Real.norm_of_nonneg (Row12.scalarLambda_pos hx).le,
    Real.sq_sqrt (Row12.scalarLambda_pos hx).le]

theorem upper_circle_nonzero {x : ℝ} {s : ℂ} (hx : 0 < x)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) : s ≠ 0 := by
  apply norm_pos_iff.mp
  rw [hs]
  exact Real.sqrt_pos.2 (Row12.scalarLambda_pos hx)

/-- A direct reverse-triangle estimate, with radius and constants fixed numerically. -/
theorem upper_betaFrameF_lower {x : ℝ} {s : ℂ}
    (hx : 0 < x) (hxsmall : x ≤ 1 / 100)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) :
    x * Real.sqrt (Row12.scalarLambda x) ≤ ‖Row12.betaFrameF (x : ℂ) s‖ := by
  let r := Real.sqrt (Row12.scalarLambda x)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hm := upper_scalarMid_lower hx hxsmall
  have hm0 : 0 ≤ Row12.scalarMid x := hx.le.trans hm
  have hmid := (Row12.betaFrame_real_agreement x).2.2.2.1
  have hlinear : ‖(2 : ℂ) * Row12.betaFrameMid (x : ℂ) * s‖ =
      2 * Row12.scalarMid x * r := by
    rw [norm_mul, norm_mul, hmid, Complex.norm_real, Real.norm_of_nonneg hm0, hs]
    norm_num [r]
  have hsmall : ‖s ^ 2 + Row12.betaFrameLambda (x : ℂ)‖ ≤ 2 * r ^ 2 := by
    calc
      _ ≤ ‖s ^ 2‖ + ‖Row12.betaFrameLambda (x : ℂ)‖ := norm_add_le _ _
      _ = 2 * r ^ 2 := by rw [norm_pow, hs, upper_lambda_norm hx]; dsimp [r]; ring
  have hid : (2 : ℂ) * Row12.betaFrameMid (x : ℂ) * s =
      (s ^ 2 + Row12.betaFrameLambda (x : ℂ)) - Row12.betaFrameF (x : ℂ) s := by
    unfold Row12.betaFrameF
    ring
  have ht : 2 * Row12.scalarMid x * r ≤ 2 * r ^ 2 + ‖Row12.betaFrameF (x : ℂ) s‖ := by
    calc
      _ = ‖(2 : ℂ) * Row12.betaFrameMid (x : ℂ) * s‖ := hlinear.symm
      _ = ‖(s ^ 2 + Row12.betaFrameLambda (x : ℂ)) - Row12.betaFrameF (x : ℂ) s‖ := by rw [hid]
      _ ≤ ‖s ^ 2 + Row12.betaFrameLambda (x : ℂ)‖ + ‖Row12.betaFrameF (x : ℂ) s‖ := norm_sub_le _ _
      _ ≤ 2 * r ^ 2 + ‖Row12.betaFrameF (x : ℂ) s‖ := add_le_add hsmall le_rfl
  have hrad : r ≤ x / 4 := upper_radius_le_quarter hx hxsmall
  have hgap : x ≤ 2 * (Row12.scalarMid x - r) := by linarith
  calc
    x * Real.sqrt (Row12.scalarLambda x) = x * r := rfl
    _ ≤ 2 * (Row12.scalarMid x - r) * r := mul_le_mul_of_nonneg_right hgap hr
    _ ≤ ‖Row12.betaFrameF (x : ℂ) s‖ := by nlinarith

theorem upper_betaFrameF_nonzero {x : ℝ} {s : ℂ}
    (hx : 0 < x) (hxsmall : x ≤ 1 / 100)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) : Row12.betaFrameF (x : ℂ) s ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (mul_pos hx (Real.sqrt_pos.2 (Row12.scalarLambda_pos hx)))
    (upper_betaFrameF_lower hx hxsmall hs)

theorem upper_betaFrameDenom_lower {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 100) :
    57624 * x ^ 4 ≤ ‖Row12.betaFrameDenom (x : ℂ)‖ := by
  have hd := upper_scalarDenom_lower hx hxsmall
  have hd0 : 0 ≤ Row12.scalarDenom x :=
    (mul_nonneg (by norm_num) (pow_nonneg hx.le 4)).trans hd
  rw [(Row12.betaFrame_real_agreement x).2.2.2.2.2.1,
    Complex.norm_real, Real.norm_of_nonneg hd0]
  exact hd

theorem upper_betaFrameDenom_nonzero {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 100) :
    Row12.betaFrameDenom (x : ℂ) ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (mul_pos (by norm_num) (pow_pos hx 4))
    (upper_betaFrameDenom_lower hx hxsmall)

theorem upper_balanced_argument_norm {x : ℝ} {s : ℂ} (hx : 0 < x)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) :
    ‖Row12.betaFrameLambda (x : ℂ) / s‖ = Real.sqrt (Row12.scalarLambda x) := by
  rw [norm_div, upper_lambda_norm hx, hs, pow_two,
    mul_div_cancel_right₀ _ (ne_of_gt (Real.sqrt_pos.2 (Row12.scalarLambda_pos hx)))]

theorem upper_betaFrame_denominator_lower {x : ℝ} {s : ℂ}
    (hx : 0 < x) (hxsmall : x ≤ 1 / 100)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) :
    57624 * x ^ 5 * Real.sqrt (Row12.scalarLambda x) ≤
      ‖Row12.betaFrameDenom (x : ℂ) * Row12.betaFrameF (x : ℂ) s‖ := by
  calc
    _ = (57624 * x ^ 4) * (x * Real.sqrt (Row12.scalarLambda x)) := by ring
    _ ≤ ‖Row12.betaFrameDenom (x : ℂ)‖ * ‖Row12.betaFrameF (x : ℂ) s‖ :=
      mul_le_mul (upper_betaFrameDenom_lower hx hxsmall) (upper_betaFrameF_lower hx hxsmall hs)
        (mul_nonneg hx.le (Real.sqrt_nonneg _)) (norm_nonneg _)
    _ = _ := (norm_mul _ _).symm

theorem upper_betaFrame_denominator_nonzero {x : ℝ} {s : ℂ}
    (hx : 0 < x) (hxsmall : x ≤ 1 / 100)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) :
    Row12.betaFrameDenom (x : ℂ) * Row12.betaFrameF (x : ℂ) s ≠ 0 :=
  mul_ne_zero (upper_betaFrameDenom_nonzero hx hxsmall) (upper_betaFrameF_nonzero hx hxsmall hs)

end Row12EulerSupport

#print axioms Row12EulerSupport.upper_scalarMid_lower
#print axioms Row12EulerSupport.upper_radius_le_quarter
#print axioms Row12EulerSupport.upper_scalarDenom_lower
#print axioms Row12EulerSupport.upper_lambda_norm
#print axioms Row12EulerSupport.upper_circle_nonzero
#print axioms Row12EulerSupport.upper_betaFrameF_lower
#print axioms Row12EulerSupport.upper_betaFrameF_nonzero
#print axioms Row12EulerSupport.upper_betaFrameDenom_lower
#print axioms Row12EulerSupport.upper_betaFrameDenom_nonzero
#print axioms Row12EulerSupport.upper_balanced_argument_norm
#print axioms Row12EulerSupport.upper_betaFrame_denominator_lower
#print axioms Row12EulerSupport.upper_betaFrame_denominator_nonzero
