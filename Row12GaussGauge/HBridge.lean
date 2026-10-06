import Row12GaussGauge.Algebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Set

namespace Row12GaussGauge

noncomputable def hV1 (h : ℝ) : ℝ :=
  (h - 8) * Real.sqrt (h + 64) / (h + 16) ^ (3 / 2 : ℝ)

noncomputable def hV2 (h : ℝ) : ℝ :=
  (h - 512) * Real.sqrt (h + 64) / (h + 256) ^ (3 / 2 : ℝ)

noncomputable def hP1 (h : ℝ) : ℝ := (1 - hV1 h) / 2
noncomputable def hP2 (h : ℝ) : ℝ := (1 - hV2 h) / 2
noncomputable def hL (h : ℝ) : ℝ := ((h + 256) / (h + 16)) ^ (1 / 4 : ℝ)
noncomputable def hQ1 (h : ℝ) : ℝ := 1728 * h / (h + 16) ^ 3
noncomputable def hQ2 (h : ℝ) : ℝ := 1728 * h ^ 2 / (h + 256) ^ 3

theorem rpow_three_halves (x : ℝ) (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem gaugeRatio_inv (D h : ℝ) (hh : 0 < h) (hD : 0 < h + D) :
    gaugeRatio D (1 / h) = Real.sqrt (h + 64) / Real.sqrt (h + D) := by
  have h64 : 0 < h + 64 := by linarith
  have hn : h ≠ 0 := ne_of_gt hh
  have hs : Real.sqrt h ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hh)
  have hd : Real.sqrt (h + D) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hD)
  have he (a : ℝ) : 1 + a * (1 / h) = (h + a) / h := by
    field_simp [hn]
  unfold gaugeRatio
  rw [he 64, he D, Real.sqrt_div h64.le, Real.sqrt_div hD.le]
  field_simp [hs, hd]

theorem signed_inv_bridge (C D h : ℝ) (hh : 0 < h) (hD : 0 < h + D) :
    (h - C) * Real.sqrt (h + 64) / (h + D) ^ (3 / 2 : ℝ) =
      (1 - C * (1 / h)) * gaugeRatio D (1 / h) / (1 + D * (1 / h)) := by
  have hn : h ≠ 0 := ne_of_gt hh
  have hd : h + D ≠ 0 := ne_of_gt hD
  have hs : Real.sqrt (h + D) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hD)
  have he : 1 + D * (1 / h) = (h + D) / h := by field_simp [hn]
  rw [rpow_three_halves _ hD, gaugeRatio_inv D h hh hD, he]
  field_simp [hn, hd, hs]

theorem hV1_eq_gauge (h : ℝ) (hh : 8 < h) :
    hV1 h = (1 - 8 * (1 / h)) * gaugeRatio 16 (1 / h) / (1 + 16 * (1 / h)) := by
  exact signed_inv_bridge 8 16 h (by linarith) (by linarith)

theorem hV2_eq_gauge (h : ℝ) (hh : 8 < h) :
    hV2 h = (1 - 512 * (1 / h)) * gaugeRatio 256 (1 / h) / (1 + 256 * (1 / h)) := by
  exact signed_inv_bridge 512 256 h (by linarith) (by linarith)

theorem hP1_eq_gauge (h : ℝ) (hh : 8 < h) : hP1 h = gaugeP1 (1 / h) := by
  unfold hP1 gaugeP1
  rw [hV1_eq_gauge h hh]

theorem hP2_eq_gauge (h : ℝ) (hh : 8 < h) : hP2 h = gaugeP2 (1 / h) := by
  unfold hP2 gaugeP2
  rw [hV2_eq_gauge h hh]

theorem bridge_gaugeL_eq_rpow (z : ℝ) (h16 : 0 < 1 + 16 * z) (h256 : 0 < 1 + 256 * z) :
    gaugeL z = ((1 + 256 * z) / (1 + 16 * z)) ^ (1 / 4 : ℝ) := by
  rw [gaugeL, Real.rpow_def_of_pos (div_pos h256 h16),
    Real.log_div (ne_of_gt h256) (ne_of_gt h16)]
  congr 1
  ring

theorem hL_eq_gauge (h : ℝ) (hh : 8 < h) : hL h = gaugeL (1 / h) := by
  have hp : 0 < h := by linarith
  have hn : h ≠ 0 := ne_of_gt hp
  have h16 : 0 < 1 + 16 * (1 / h) := by positivity
  have h256 : 0 < 1 + 256 * (1 / h) := by positivity
  have he : (h + 256) / (h + 16) =
      (1 + 256 * (1 / h)) / (1 + 16 * (1 / h)) := by
    field_simp [hn, ne_of_gt h16, ne_of_gt (show 0 < h + 16 by linarith)]
  rw [hL, bridge_gaugeL_eq_rpow _ h16 h256, he]

theorem hQ1_quadratic (h : ℝ) (hh : 8 < h) :
    4 * hP1 h * (1 - hP1 h) = hQ1 h := by
  have hp : 0 < h := by linarith
  rw [hP1_eq_gauge h hh, gaugeP1_quadratic (1 / h) (by positivity) (by positivity)]
  unfold hQ1
  field_simp [ne_of_gt hp, ne_of_gt (show 0 < h + 16 by linarith)]

theorem hQ2_quadratic (h : ℝ) (hh : 8 < h) :
    4 * hP2 h * (1 - hP2 h) = hQ2 h := by
  have hp : 0 < h := by linarith
  rw [hP2_eq_gauge h hh, gaugeP2_quadratic (1 / h) (by positivity) (by positivity)]
  unfold hQ2
  field_simp [ne_of_gt hp, ne_of_gt (show 0 < h + 256 by linarith)]

theorem hP1_eq_gaussP (h : ℝ) (hh : 8 < h) : hP1 h = Row12.gaussP (hQ1 h) := by
  have hv : 0 ≤ hV1 h := by
    have h8 : 0 < h - 8 := sub_pos.2 hh
    have h64 : 0 < h + 64 := by linarith
    have h16 : 0 < h + 16 := by linarith
    unfold hV1
    positivity
  have hq := hQ1_quadratic h hh
  have he : 1 - hQ1 h = hV1 h ^ 2 := by
    dsimp only [hP1] at hq
    nlinarith
  have hs : Real.sqrt (1 - hQ1 h) = hV1 h := by rw [he, Real.sqrt_sq hv]
  rw [hP1, Row12.gaussP, hs]

theorem hP2_eq_complement (h : ℝ) (hh : 8 < h) (h512 : h < 512) :
    hP2 h = 1 - Row12.gaussP (hQ2 h) := by
  have hv : 0 ≤ -hV2 h := by
    unfold hV2
    have hd : 0 < (h + 256) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hn : (h - 512) * Real.sqrt (h + 64) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)
    exact neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg hn hd.le)
  have hq := hQ2_quadratic h hh
  have he : 1 - hQ2 h = (-hV2 h) ^ 2 := by
    dsimp only [hP2] at hq
    nlinarith
  have hs : Real.sqrt (1 - hQ2 h) = -hV2 h := by rw [he, Real.sqrt_sq hv]
  rw [hP2, Row12.gaussP, hs]
  ring

theorem gaugeP1_contact : gaugeP1 (1 / 64 : ℝ) = Row12.gaussP (27 / 125) := by
  let v : ℝ := (1 - 8 * (1 / 64 : ℝ)) * gaugeRatio 16 (1 / 64) /
    (1 + 16 * (1 / 64 : ℝ))
  have hr := gaugeRatio_sq 16 (1 / 64 : ℝ) (by norm_num) (by norm_num)
  have hv : 0 ≤ v := by unfold v gaugeRatio; positivity
  have hv2 : v ^ 2 = 1 - (27 / 125 : ℝ) := by
    dsimp only [v]
    norm_num at hr ⊢
    nlinarith [hr]
  have hs : v = Real.sqrt (1 - (27 / 125 : ℝ)) := by
    exact ((Real.sqrt_eq_iff_eq_sq (by norm_num) hv).2 hv2.symm).symm
  change (1 - v) / 2 = (1 - Real.sqrt (1 - (27 / 125 : ℝ))) / 2
  rw [hs]

theorem gaugeP2_contact : gaugeP2 (1 / 64 : ℝ) = 1 - Row12.gaussP (27 / 125) := by
  let v : ℝ := (1 - 512 * (1 / 64 : ℝ)) * gaugeRatio 256 (1 / 64) /
    (1 + 256 * (1 / 64 : ℝ))
  have hr := gaugeRatio_sq 256 (1 / 64 : ℝ) (by norm_num) (by norm_num)
  have hv : 0 ≤ -v := by
    have hR : 0 ≤ gaugeRatio 256 (1 / 64 : ℝ) := by unfold gaugeRatio; positivity
    dsimp only [v]
    nlinarith [hR]
  have hv2 : (-v) ^ 2 = 1 - (27 / 125 : ℝ) := by
    dsimp only [v]
    norm_num at hr ⊢
    nlinarith [hr]
  have hs : -v = Real.sqrt (1 - (27 / 125 : ℝ)) := by
    exact ((Real.sqrt_eq_iff_eq_sq (by norm_num) hv).2 hv2.symm).symm
  change (1 - v) / 2 = 1 - (1 - Real.sqrt (1 - (27 / 125 : ℝ))) / 2
  linarith

theorem gaugeL_contact : gaugeL (1 / 64 : ℝ) = Real.sqrt 2 := by
  rw [bridge_gaugeL_eq_rpow _ (by norm_num) (by norm_num)]
  norm_num
  have he := Real.rpow_mul (show 0 ≤ (2 : ℝ) by norm_num) (2 : ℝ) (1 / 4 : ℝ)
  norm_num at he
  rw [← he, ← Real.sqrt_eq_rpow]

theorem gaugeRatio_contact_eq :
    gaugeRatio 16 (1 / 64 : ℝ) = 2 * gaugeRatio 256 (1 / 64 : ℝ) := by
  have h1 := gaugeRatio_sq 16 (1 / 64 : ℝ) (by norm_num) (by norm_num)
  have h2 := gaugeRatio_sq 256 (1 / 64 : ℝ) (by norm_num) (by norm_num)
  have hp1 : 0 ≤ gaugeRatio 16 (1 / 64 : ℝ) := by unfold gaugeRatio; positivity
  have hp2 : 0 ≤ gaugeRatio 256 (1 / 64 : ℝ) := by unfold gaugeRatio; positivity
  norm_num at h1 h2
  nlinarith

theorem gaugeK_contact_eq : gaugeK1 (1 / 64 : ℝ) = gaugeK2 (1 / 64 : ℝ) := by
  unfold gaugeK1 gaugeK2 gaugeBase
  norm_num
  rw [gaugeRatio_contact_eq]
  ring

theorem gaugeK1_contact_normalization :
    Real.sqrt (1 - (27 / 125 : ℝ)) * gaugeK1 (1 / 64 : ℝ) = (3024 / 625 : ℝ) := by
  have hp := gaugeP1_contact
  have hr := gaugeRatio_sq 16 (1 / 64 : ℝ) (by norm_num) (by norm_num)
  have hs : Real.sqrt (1 - (27 / 125 : ℝ)) =
      (7 / 10 : ℝ) * gaugeRatio 16 (1 / 64 : ℝ) := by
    unfold gaugeP1 Row12.gaussP at hp
    norm_num at hp ⊢
    linarith
  rw [hs]
  unfold gaugeK1 gaugeBase
  norm_num at hr ⊢
  nlinarith

theorem gaugeMu_contact : gaugeMu (1 / 64 : ℝ) = (48 / 5 : ℝ) := by
  norm_num [gaugeMu]

theorem gaugeK2_contact_normalization :
    4 * Real.sqrt (1 - (27 / 125 : ℝ)) * gaugeK2 (1 / 64 : ℝ) =
      (27 / 125 : ℝ) * (448 / 5) := by
  rw [← gaugeK_contact_eq]
  nlinarith [gaugeK1_contact_normalization]

theorem gaugeK2_contact : gaugeK2 (1 / 64 : ℝ) =
    (216 / 25 : ℝ) * Real.sqrt 2 / Real.sqrt 5 := by
  unfold gaugeK2 gaugeBase gaugeRatio
  norm_num
  ring

theorem gaugeK2_contact_ne_zero : gaugeK2 (1 / 64 : ℝ) ≠ 0 := by
  intro hk
  have he := gaugeK2_contact_normalization
  rw [hk] at he
  norm_num at he

theorem hP1_contact : hP1 64 = Row12.gaussP (27 / 125) := by
  rw [hP1_eq_gauge 64 (by norm_num), gaugeP1_contact]

theorem hP2_contact : hP2 64 = 1 - Row12.gaussP (27 / 125) := by
  rw [hP2_eq_gauge 64 (by norm_num), gaugeP2_contact]

theorem hL_contact : hL 64 = Real.sqrt 2 := by
  rw [hL_eq_gauge 64 (by norm_num), gaugeL_contact]

theorem hQ1_contact : hQ1 64 = (27 / 125 : ℝ) := by norm_num [hQ1]
theorem hQ2_contact : hQ2 64 = (27 / 125 : ℝ) := by norm_num [hQ2]

theorem hQ1_hasDerivAt (h : ℝ) (hh : 8 < h) :
    HasDerivAt hQ1 (1728 * (16 - 2 * h) / (h + 16) ^ 4) h := by
  have hn : h + 16 ≠ 0 := ne_of_gt (by linarith : 0 < h + 16)
  have hd := ((hasDerivAt_id h).const_mul 1728).div
    (((hasDerivAt_id h).add_const 16).pow 3) (pow_ne_zero 3 hn)
  have he : (1728 * 1 * (h + 16) ^ 3 - 1728 * h *
      (3 * (h + 16) ^ (3 - 1) * 1)) / ((h + 16) ^ 3) ^ 2 =
      1728 * (16 - 2 * h) / (h + 16) ^ 4 := by
    field_simp [hn]
    ring
  exact hd.congr_deriv he

theorem hQ2_hasDerivAt (h : ℝ) (hh : 8 < h) :
    HasDerivAt hQ2 (1728 * h * (512 - h) / (h + 256) ^ 4) h := by
  have hn : h + 256 ≠ 0 := ne_of_gt (by linarith : 0 < h + 256)
  have hd := (((hasDerivAt_id h).pow 2).const_mul 1728).div
    (((hasDerivAt_id h).add_const 256).pow 3) (pow_ne_zero 3 hn)
  have he : (1728 * (2 * h ^ (2 - 1) * 1) * (h + 256) ^ 3 - 1728 * h ^ 2 *
      (3 * (h + 256) ^ (3 - 1) * 1)) / ((h + 256) ^ 3) ^ 2 =
      1728 * h * (512 - h) / (h + 256) ^ 4 := by
    field_simp [hn]
    ring
  exact hd.congr_deriv he

theorem hQ1_contact_deriv : deriv hQ1 64 / hQ1 64 = (-7 / 320 : ℝ) := by
  rw [(hQ1_hasDerivAt 64 (by norm_num)).deriv, hQ1_contact]
  norm_num

theorem hQ2_contact_deriv : deriv hQ2 64 / hQ2 64 = (7 / 320 : ℝ) := by
  rw [(hQ2_hasDerivAt 64 (by norm_num)).deriv, hQ2_contact]
  norm_num

theorem hL_eq_exp (h : ℝ) (hh : 8 < h) :
    hL h = Real.exp ((Real.log (h + 256) - Real.log (h + 16)) / 4) := by
  have h16 : 0 < h + 16 := by linarith
  have h256 : 0 < h + 256 := by linarith
  rw [hL, Real.rpow_def_of_pos (div_pos h256 h16),
    Real.log_div (ne_of_gt h256) (ne_of_gt h16)]
  congr 1
  ring

theorem hL_hasDerivAt (h : ℝ) (hh : 8 < h) :
    HasDerivAt hL (hL h * (-60 / ((h + 16) * (h + 256)))) h := by
  have h16 : h + 16 ≠ 0 := ne_of_gt (by linarith : 0 < h + 16)
  have h256 : h + 256 ≠ 0 := ne_of_gt (by linarith : 0 < h + 256)
  have hd := ((((hasDerivAt_id h).add_const 256).log h256).sub
    (((hasDerivAt_id h).add_const 16).log h16)).div_const 4 |>.exp
  have he : Real.exp ((Real.log (h + 256) - Real.log (h + 16)) / 4) *
      ((1 / (h + 256) - 1 / (h + 16)) / 4) =
      hL h * (-60 / ((h + 16) * (h + 256))) := by
    rw [hL_eq_exp h hh]
    field_simp [h16, h256]
    ring
  apply (hd.congr_deriv he).congr_of_eventuallyEq
  have hn : Ioi (8 : ℝ) ∈ nhds h := isOpen_Ioi.mem_nhds hh
  filter_upwards [hn] with x hx
  exact hL_eq_exp x hx

theorem hL_contact_deriv : deriv hL 64 / hL 64 = (-3 / 1280 : ℝ) := by
  have hs : hL 64 ≠ 0 := by rw [hL_contact]; exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [(hL_hasDerivAt 64 (by norm_num)).deriv]
  field_simp [hs]
  norm_num

end Row12GaussGauge
