import Row12.GaussQuadratic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Filter Set Row12

namespace Row12GaussGauge

noncomputable def gaugeRatio (D z : ℝ) : ℝ :=
  Real.sqrt (1 + 64*z) / Real.sqrt (1 + D*z)

noncomputable def gaugeP1 (z : ℝ) : ℝ :=
  (1 - (1-8*z)*gaugeRatio 16 z/(1+16*z))/2

noncomputable def gaugeP2 (z : ℝ) : ℝ :=
  (1 - (1-512*z)*gaugeRatio 256 z/(1+256*z))/2

noncomputable def gaugeL (z : ℝ) : ℝ :=
  Real.exp ((Real.log (1+256*z)-Real.log (1+16*z))/4)

noncomputable def gaugeY1 (z : ℝ) : ℝ := gaussA (gaugeP1 z)
noncomputable def gaugeY2 (z : ℝ) : ℝ := gaussA (gaugeP2 z)

noncomputable def gaugeBase (C D z : ℝ) : ℝ :=
  C*gaugeRatio D z/((1+64*z)*(1+D*z)^2)

noncomputable def gaugeK1 (z : ℝ) : ℝ := z*gaugeBase 864 16 z
noncomputable def gaugeK2 (z : ℝ) : ℝ := gaugeBase 432 256 z

noncomputable def gaugeT (D z : ℝ) : ℝ :=
  -32/(1+64*z)-5*D/(2*(1+D*z))

noncomputable def gaugeB1 (z : ℝ) : ℝ :=
  z*(-8/(1+16*z)+32/(1+64*z))
noncomputable def gaugeC1 (z : ℝ) : ℝ :=
  -240*z^2/((1+64*z)*(1+16*z)^2)
noncomputable def gaugeB2 (z : ℝ) : ℝ :=
  z*(-128/(1+256*z)+32/(1+64*z))
noncomputable def gaugeC2 (z : ℝ) : ℝ :=
  -60*z/((1+64*z)*(1+256*z)^2)

noncomputable def gaugeMu (z : ℝ) : ℝ := 60/((1+16*z)*(1+256*z))

theorem gaugeRoot_hasDerivAt (D z : ℝ) (hp : 0 < 1+D*z) :
    HasDerivAt (fun x : ℝ => Real.sqrt (1+D*x)) (D/(2*Real.sqrt (1+D*z))) z := by
  simpa only [Pi.add_apply, id_eq, zero_add, mul_one] using
    ((hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul D)).sqrt (ne_of_gt hp)

theorem gaugeRoot_analyticAt (D z : ℝ) (hp : 0 < 1+D*z) :
    AnalyticAt ℝ (fun x : ℝ => Real.sqrt (1+D*x)) z := by
  have ha : AnalyticAt ℝ (fun x : ℝ => 1+D*x) z := by fun_prop
  have hl : AnalyticAt ℝ (fun x : ℝ => Real.log (1+D*x)) z :=
    ha.log hp
  have hh : AnalyticAt ℝ (fun x : ℝ => Real.log (1+D*x)*(1/2)) z := by fun_prop
  apply hh.rexp'.congr
  have hn : {x : ℝ | 0 < 1+D*x} ∈ nhds z :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hp
  filter_upwards [hn] with x hx
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]

theorem gaugeRatio_sq (D z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+D*z) :
    gaugeRatio D z ^ 2 = (1+64*z)/(1+D*z) := by
  rw [gaugeRatio, div_pow, Real.sq_sqrt hS.le, Real.sq_sqrt hD.le]

theorem gaugeRatio_hasDerivAt (D z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+D*z) :
    HasDerivAt (gaugeRatio D)
      (gaugeRatio D z*(32/(1+64*z)-D/(2*(1+D*z)))) z := by
  have hs : Real.sqrt (1+64*z) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hS)
  have hd : Real.sqrt (1+D*z) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hD)
  have hs2 := Real.sq_sqrt hS.le
  have hd2 := Real.sq_sqrt hD.le
  have hder := (gaugeRoot_hasDerivAt 64 z hS).div (gaugeRoot_hasDerivAt D z hD) hd
  have he : (64/(2*Real.sqrt (1+64*z))*Real.sqrt (1+D*z) -
      Real.sqrt (1+64*z)*(D/(2*Real.sqrt (1+D*z))))/Real.sqrt (1+D*z)^2 =
      gaugeRatio D z*(32/(1+64*z)-D/(2*(1+D*z))) := by
    unfold gaugeRatio
    generalize Real.sqrt (1+64*z) = s at hs hs2 ⊢
    generalize Real.sqrt (1+D*z) = d at hd hd2 ⊢
    rw [← hs2, ← hd2]
    field_simp [hs, hd]
    ring
  convert! hder.congr_deriv he using 1

theorem gaugeRatio_analyticAt (D z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+D*z) :
    AnalyticAt ℝ (gaugeRatio D) z := by
  exact (gaugeRoot_analyticAt 64 z hS).div (gaugeRoot_analyticAt D z hD)
    (ne_of_gt (Real.sqrt_pos.2 hD))

theorem gaugeP1_hasDerivAt (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+16*z) :
    HasDerivAt gaugeP1 (gaugeK1 z) z := by
  have hR := gaugeRatio_hasDerivAt 16 z hS hD
  have ht := ((hasDerivAt_id z).const_mul 8).const_sub 1
  have hd := (hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul 16)
  have hp := (((ht.mul hR).div hd (ne_of_gt hD)).const_sub 1).div_const 2
  have he : -((( -(8*1)*gaugeRatio 16 z + (1-8*z)*
      (gaugeRatio 16 z*(32/(1+64*z)-16/(2*(1+16*z)))))*(1+16*z) -
      ((1-8*z)*gaugeRatio 16 z)*(0+16*1))/(1+16*z)^2)/2 = gaugeK1 z := by
    unfold gaugeK1 gaugeBase
    generalize hSe : 1+64*z = s at hS ⊢
    generalize hDe : 1+16*z = d at hD ⊢
    field_simp [ne_of_gt hS, ne_of_gt hD]
    rw [← hSe, ← hDe]
    ring
  convert! hp.congr_deriv he using 1

theorem gaugeP2_hasDerivAt (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+256*z) :
    HasDerivAt gaugeP2 (gaugeK2 z) z := by
  have hR := gaugeRatio_hasDerivAt 256 z hS hD
  have ht := ((hasDerivAt_id z).const_mul 512).const_sub 1
  have hd := (hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul 256)
  have hp := (((ht.mul hR).div hd (ne_of_gt hD)).const_sub 1).div_const 2
  have he : -(((-(512*1)*gaugeRatio 256 z + (1-512*z)*
      (gaugeRatio 256 z*(32/(1+64*z)-256/(2*(1+256*z)))))*(1+256*z) -
      ((1-512*z)*gaugeRatio 256 z)*(0+256*1))/(1+256*z)^2)/2 = gaugeK2 z := by
    unfold gaugeK2 gaugeBase
    generalize hSe : 1+64*z = s at hS ⊢
    generalize hDe : 1+256*z = d at hD ⊢
    field_simp [ne_of_gt hS, ne_of_gt hD]
    rw [← hSe, ← hDe]
    ring
  convert! hp.congr_deriv he using 1

theorem gaugeBase_hasDerivAt (C D z : ℝ) (hS : 0 < 1+64*z)
    (hD : 0 < 1+D*z) :
    HasDerivAt (gaugeBase C D) (gaugeBase C D z*gaugeT D z) z := by
  have hR := gaugeRatio_hasDerivAt D z hS hD
  have hSder := (hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul 64)
  have hDder := (hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul D)
  have hd := ((hR.const_mul C).div (hSder.mul (hDder.pow 2))
    (mul_ne_zero (ne_of_gt hS) (pow_ne_zero 2 (ne_of_gt hD))))
  have he : ((C*
      (gaugeRatio D z*(32/(1+64*z)-D/(2*(1+D*z)))))*((1+64*z)*(1+D*z)^2) -
      (C*gaugeRatio D z)*((0+64*1)*(1+D*z)^2 +
      (1+64*z)*(2*(1+D*z)^(2-1)*(0+D*1))))/((1+64*z)*(1+D*z)^2)^2 =
      gaugeBase C D z*gaugeT D z := by
    unfold gaugeBase gaugeT
    generalize 1+64*z = s at hS ⊢
    generalize 1+D*z = d at hD ⊢
    field_simp [ne_of_gt hS, ne_of_gt hD]
    ring
  convert! hd.congr_deriv he using 1

theorem gaugeK1_hasDerivAt (z : ℝ) (hz : z ≠ 0) (hS : 0 < 1+64*z)
    (hD : 0 < 1+16*z) :
    HasDerivAt gaugeK1 (gaugeK1 z*(1/z+gaugeT 16 z)) z := by
  have hd := (hasDerivAt_id z).mul (gaugeBase_hasDerivAt 864 16 z hS hD)
  have he : 1*gaugeBase 864 16 z + z*(gaugeBase 864 16 z*gaugeT 16 z) =
      gaugeK1 z*(1/z+gaugeT 16 z) := by
    unfold gaugeK1
    field_simp [hz]
  convert! hd.congr_deriv he using 1

theorem gaugeK2_hasDerivAt (z : ℝ) (hS : 0 < 1+64*z)
    (hD : 0 < 1+256*z) :
    HasDerivAt gaugeK2 (gaugeK2 z*gaugeT 256 z) z :=
  gaugeBase_hasDerivAt 432 256 z hS hD

theorem gaugeP1_quadratic (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+16*z) :
    4*gaugeP1 z*(1-gaugeP1 z) = 1728*z^2/(1+16*z)^3 := by
  have hs := gaugeRatio_sq 16 z hS hD
  unfold gaugeP1
  generalize hdEq : 1+16*z = d at hD hs ⊢
  field_simp [ne_of_gt hD] at hs ⊢
  rw [← hdEq] at hs ⊢
  linear_combination - 4*(1-8*z)^2 * hs

theorem gaugeP2_quadratic (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+256*z) :
    4*gaugeP2 z*(1-gaugeP2 z) = 1728*z/(1+256*z)^3 := by
  have hs := gaugeRatio_sq 256 z hS hD
  unfold gaugeP2
  generalize hdEq : 1+256*z = d at hD hs ⊢
  field_simp [ne_of_gt hD] at hs ⊢
  rw [← hdEq] at hs ⊢
  linear_combination - 4*(1-512*z)^2 * hs

theorem gaugeP1_norm_lt_one (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/8) :
    ‖gaugeP1 z‖ < 1 := by
  have hS : 0 < 1+64*z := by positivity
  have hD : 0 < 1+16*z := by positivity
  have hq := gaugeP1_quadratic z hS hD
  have hqp : 0 < 1728*z^2/(1+16*z)^3 := by positivity
  have ht : 0 < 1-8*z := by linarith
  have hr : 0 < gaugeRatio 16 z := by
    unfold gaugeRatio
    exact div_pos (Real.sqrt_pos.2 hS) (Real.sqrt_pos.2 hD)
  have hp : gaugeP1 z < 1/2 := by
    unfold gaugeP1
    have hv : 0 < (1-8*z)*gaugeRatio 16 z/(1+16*z) := by positivity
    linarith
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> nlinarith

theorem gaugeP2_norm_lt_one (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/8) :
    ‖gaugeP2 z‖ < 1 := by
  have ht : 0 < 1-8*z := by linarith
  have hS : 0 < 1+64*z := by linarith
  have hD : 0 < 1+256*z := by positivity
  have hq := gaugeP2_quadratic z hS hD
  have hqp : 0 < 1728*z/(1+256*z)^3 := by positivity
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> nlinarith

theorem gaugeP1_analyticAt (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+16*z) :
    AnalyticAt ℝ gaugeP1 z := by
  have hR := gaugeRatio_analyticAt 16 z hS hD
  unfold gaugeP1
  fun_prop (disch := exact ne_of_gt hD)

theorem gaugeP2_analyticAt (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+256*z) :
    AnalyticAt ℝ gaugeP2 z := by
  have hR := gaugeRatio_analyticAt 256 z hS hD
  unfold gaugeP2
  fun_prop (disch := exact ne_of_gt hD)

theorem gaugeP1_zero : gaugeP1 0 = 0 := by norm_num [gaugeP1, gaugeRatio]
theorem gaugeP2_zero : gaugeP2 0 = 0 := by norm_num [gaugeP2, gaugeRatio]
theorem gaugeY1_zero : gaugeY1 0 = 1 := by simp [gaugeY1, gaugeP1_zero, gaussA_zero]
theorem gaugeY2_zero : gaugeY2 0 = 1 := by simp [gaugeY2, gaugeP2_zero, gaussA_zero]
theorem gaugeL_zero : gaugeL 0 = 1 := by norm_num [gaugeL]

theorem gaugeY1_analyticAt_zero : AnalyticAt ℝ gaugeY1 0 := by
  have ha : AnalyticAt ℝ gaussA (gaugeP1 0) := by
    rw [gaugeP1_zero]
    exact gaussA_analyticAt 0 (by norm_num)
  exact ha.comp (gaugeP1_analyticAt 0 (by norm_num) (by norm_num))

theorem gaugeY2_analyticAt_zero : AnalyticAt ℝ gaugeY2 0 := by
  have ha : AnalyticAt ℝ gaussA (gaugeP2 0) := by
    rw [gaugeP2_zero]
    exact gaussA_analyticAt 0 (by norm_num)
  exact ha.comp (gaugeP2_analyticAt 0 (by norm_num) (by norm_num))

theorem gaugeY1_analyticAt (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/8) :
    AnalyticAt ℝ gaugeY1 z :=
  (gaussA_analyticAt (gaugeP1 z) (gaugeP1_norm_lt_one z hz0 hz1)).comp
    (gaugeP1_analyticAt z (by positivity) (by positivity))

theorem gaugeY2_analyticAt (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/8) :
    AnalyticAt ℝ gaugeY2 z :=
  (gaussA_analyticAt (gaugeP2 z) (gaugeP2_norm_lt_one z hz0 hz1)).comp
    (gaugeP2_analyticAt z (by positivity) (by positivity))

theorem gaugeRatio_pos (D z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+D*z) :
    0 < gaugeRatio D z := by
  exact div_pos (Real.sqrt_pos.2 hS) (Real.sqrt_pos.2 hD)

theorem gaugeRatio_zero (D : ℝ) : gaugeRatio D 0 = 1 := by
  norm_num [gaugeRatio]

theorem gaugeBase_zero (C D : ℝ) : gaugeBase C D 0 = C := by
  norm_num [gaugeBase, gaugeRatio]

theorem gaugeK1_zero : gaugeK1 0 = 0 := by
  norm_num [gaugeK1]

theorem gaugeK2_zero : gaugeK2 0 = 432 := by
  norm_num [gaugeK2, gaugeBase_zero]

theorem gaugeB1_zero : gaugeB1 0 = 0 := by
  norm_num [gaugeB1]

theorem gaugeB2_zero : gaugeB2 0 = 0 := by
  norm_num [gaugeB2]

theorem gaugeC1_zero : gaugeC1 0 = 0 := by
  norm_num [gaugeC1]

theorem gaugeC2_zero : gaugeC2 0 = 0 := by
  norm_num [gaugeC2]

theorem gaugeMu_zero : gaugeMu 0 = 60 := by
  norm_num [gaugeMu]

theorem gaugeB1_analyticAt (z : ℝ) (hS : 1+64*z ≠ 0)
    (hD : 1+16*z ≠ 0) :
    AnalyticAt ℝ gaugeB1 z := by
  unfold gaugeB1
  fun_prop (disch := assumption)

theorem gaugeB2_analyticAt (z : ℝ) (hS : 1+64*z ≠ 0)
    (hD : 1+256*z ≠ 0) :
    AnalyticAt ℝ gaugeB2 z := by
  unfold gaugeB2
  fun_prop (disch := assumption)

theorem gaugeC1_analyticAt (z : ℝ) (hS : 1+64*z ≠ 0)
    (hD : 1+16*z ≠ 0) : AnalyticAt ℝ gaugeC1 z := by
  have hd : (1+64*z)*(1+16*z)^2 ≠ 0 := mul_ne_zero hS (pow_ne_zero 2 hD)
  unfold gaugeC1
  fun_prop (disch := assumption)

theorem gaugeC2_analyticAt (z : ℝ) (hS : 1+64*z ≠ 0)
    (hD : 1+256*z ≠ 0) : AnalyticAt ℝ gaugeC2 z := by
  have hd : (1+64*z)*(1+256*z)^2 ≠ 0 := mul_ne_zero hS (pow_ne_zero 2 hD)
  unfold gaugeC2
  fun_prop (disch := assumption)

theorem gaugeB1_continuousAt_zero : ContinuousAt gaugeB1 0 :=
  (gaugeB1_analyticAt 0 (by norm_num) (by norm_num)).continuousAt

theorem gaugeB2_continuousAt_zero : ContinuousAt gaugeB2 0 :=
  (gaugeB2_analyticAt 0 (by norm_num) (by norm_num)).continuousAt

theorem gaugeC1_continuousAt_zero : ContinuousAt gaugeC1 0 :=
  (gaugeC1_analyticAt 0 (by norm_num) (by norm_num)).continuousAt

theorem gaugeC2_continuousAt_zero : ContinuousAt gaugeC2 0 :=
  (gaugeC2_analyticAt 0 (by norm_num) (by norm_num)).continuousAt

end Row12GaussGauge

#print axioms Row12GaussGauge.gaugeRoot_hasDerivAt
#print axioms Row12GaussGauge.gaugeRoot_analyticAt
#print axioms Row12GaussGauge.gaugeRatio_sq
#print axioms Row12GaussGauge.gaugeRatio_hasDerivAt
#print axioms Row12GaussGauge.gaugeRatio_analyticAt
#print axioms Row12GaussGauge.gaugeP1_hasDerivAt
#print axioms Row12GaussGauge.gaugeP2_hasDerivAt
#print axioms Row12GaussGauge.gaugeBase_hasDerivAt
#print axioms Row12GaussGauge.gaugeK1_hasDerivAt
#print axioms Row12GaussGauge.gaugeK2_hasDerivAt
#print axioms Row12GaussGauge.gaugeP1_quadratic
#print axioms Row12GaussGauge.gaugeP2_quadratic
#print axioms Row12GaussGauge.gaugeP1_norm_lt_one
#print axioms Row12GaussGauge.gaugeP2_norm_lt_one
#print axioms Row12GaussGauge.gaugeP1_analyticAt
#print axioms Row12GaussGauge.gaugeP2_analyticAt
#print axioms Row12GaussGauge.gaugeP1_zero
#print axioms Row12GaussGauge.gaugeP2_zero
#print axioms Row12GaussGauge.gaugeY1_zero
#print axioms Row12GaussGauge.gaugeY2_zero
#print axioms Row12GaussGauge.gaugeL_zero
#print axioms Row12GaussGauge.gaugeY1_analyticAt_zero
#print axioms Row12GaussGauge.gaugeY2_analyticAt_zero
#print axioms Row12GaussGauge.gaugeY1_analyticAt
#print axioms Row12GaussGauge.gaugeY2_analyticAt
#print axioms Row12GaussGauge.gaugeRatio_pos
#print axioms Row12GaussGauge.gaugeRatio_zero
#print axioms Row12GaussGauge.gaugeBase_zero
#print axioms Row12GaussGauge.gaugeK1_zero
#print axioms Row12GaussGauge.gaugeK2_zero
#print axioms Row12GaussGauge.gaugeB1_zero
#print axioms Row12GaussGauge.gaugeB2_zero
#print axioms Row12GaussGauge.gaugeC1_zero
#print axioms Row12GaussGauge.gaugeC2_zero
#print axioms Row12GaussGauge.gaugeMu_zero
#print axioms Row12GaussGauge.gaugeB1_analyticAt
#print axioms Row12GaussGauge.gaugeB2_analyticAt
#print axioms Row12GaussGauge.gaugeC1_analyticAt
#print axioms Row12GaussGauge.gaugeC2_analyticAt
#print axioms Row12GaussGauge.gaugeB1_continuousAt_zero
#print axioms Row12GaussGauge.gaugeB2_continuousAt_zero
#print axioms Row12GaussGauge.gaugeC1_continuousAt_zero
#print axioms Row12GaussGauge.gaugeC2_continuousAt_zero
