import Row12GaussGauge.Algebra

open Filter Set
open Row12

namespace Row12GaussGauge

theorem gaugeK1_sq (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+16*z) :
    gaugeK1 z ^ 2 = 746496*z^2/((1+64*z)*(1+16*z)^5) := by
  have hr := gaugeRatio_sq 16 z hS hD
  simp only [gaugeK1, gaugeBase, mul_pow, div_pow]
  rw [hr]
  field_simp [ne_of_gt hS, ne_of_gt hD]
  ring

theorem gaugeK2_sq (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+256*z) :
    gaugeK2 z ^ 2 = 186624/((1+64*z)*(1+256*z)^5) := by
  have hr := gaugeRatio_sq 256 z hS hD
  simp only [gaugeK2, gaugeBase, mul_pow, div_pow]
  rw [hr]
  field_simp [ne_of_gt hS, ne_of_gt hD]
  ring

theorem gaugeP1_product (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+16*z) :
    gaugeP1 z*(1-gaugeP1 z) = 432*z^2/(1+16*z)^3 := by
  linear_combination gaugeP1_quadratic z hS hD / 4

theorem gaugeP2_product (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+256*z) :
    gaugeP2 z*(1-gaugeP2 z) = 432*z/(1+256*z)^3 := by
  linear_combination gaugeP2_quadratic z hS hD / 4

theorem gaugeP1_pullback_first (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    gaugeP1 z*(1-gaugeP1 z)*
        (z*gaugeK1 z+z^2*(gaugeK1 z*(1/z+gaugeT 16 z))+
          gaugeB1 z*z*gaugeK1 z) =
      z^2*gaugeK1 z^2*(1-2*gaugeP1 z) := by
  have hS : 0 < 1+64*z := by positivity
  have hD : 0 < 1+16*z := by positivity
  have ht : 1-8*z ≠ 0 := by linarith
  rw [gaugeP1_product z hS hD, gaugeK1_sq z hS hD]
  unfold gaugeK1 gaugeBase gaugeT gaugeB1 gaugeP1
  field_simp [ne_of_gt hz, ne_of_gt hS, ne_of_gt hD, ht]
  ring

theorem gaugeP2_pullback_first (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    gaugeP2 z*(1-gaugeP2 z)*
        (z*gaugeK2 z+z^2*(gaugeK2 z*gaugeT 256 z)+
          gaugeB2 z*z*gaugeK2 z) =
      z^2*gaugeK2 z^2*(1-2*gaugeP2 z) := by
  have hS : 0 < 1+64*z := by positivity
  have hD : 0 < 1+256*z := by positivity
  have ht : 1-8*z ≠ 0 := by linarith
  rw [gaugeP2_product z hS hD, gaugeK2_sq z hS hD]
  unfold gaugeK2 gaugeBase gaugeT gaugeB2 gaugeP2
  field_simp [ne_of_gt hz, ne_of_gt hS, ne_of_gt hD, ht]
  ring

theorem gaugeP1_pullback_constant (z : ℝ) (hz : 0 < z) :
    gaugeP1 z*(1-gaugeP1 z)*gaugeC1 z = -(5/36:ℝ)*z^2*gaugeK1 z^2 := by
  have hS : 0 < 1+64*z := by positivity
  have hD : 0 < 1+16*z := by positivity
  rw [gaugeP1_product z hS hD, gaugeK1_sq z hS hD]
  unfold gaugeC1
  field_simp [ne_of_gt hS, ne_of_gt hD]
  ring

theorem gaugeP2_pullback_constant (z : ℝ) (hz : 0 < z) :
    gaugeP2 z*(1-gaugeP2 z)*gaugeC2 z = -(5/36:ℝ)*z^2*gaugeK2 z^2 := by
  have hS : 0 < 1+64*z := by positivity
  have hD : 0 < 1+256*z := by positivity
  rw [gaugeP2_product z hS hD, gaugeK2_sq z hS hD]
  unfold gaugeC2
  field_simp [ne_of_gt hS, ne_of_gt hD]
  ring

theorem gaugeY1_hasDerivAt (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    HasDerivAt gaugeY1 (deriv gaussA (gaugeP1 z)*gaugeK1 z) z := by
  exact (gaussA_analyticAt (gaugeP1 z) (gaugeP1_norm_lt_one z hz hz1)).differentiableAt.hasDerivAt.comp z
      (gaugeP1_hasDerivAt z (by positivity) (by positivity))

theorem gaugeY2_hasDerivAt (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    HasDerivAt gaugeY2 (deriv gaussA (gaugeP2 z)*gaugeK2 z) z := by
  exact (gaussA_analyticAt (gaugeP2 z) (gaugeP2_norm_lt_one z hz hz1)).differentiableAt.hasDerivAt.comp z
      (gaugeP2_hasDerivAt z (by positivity) (by positivity))

theorem gaugeY1_second_deriv (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    deriv (deriv gaugeY1) z =
      deriv (deriv gaussA) (gaugeP1 z)*gaugeK1 z^2+
        deriv gaussA (gaugeP1 z)*(gaugeK1 z*(1/z+gaugeT 16 z)) := by
  have ha := (gaussA_analyticAt (gaugeP1 z) (gaugeP1_norm_lt_one z hz hz1)).deriv.differentiableAt.hasDerivAt
  have hd := (ha.comp z (gaugeP1_hasDerivAt z (by positivity) (by positivity))).mul
    (gaugeK1_hasDerivAt z (ne_of_gt hz) (by positivity) (by positivity))
  have he : deriv gaugeY1 =ᶠ[nhds z]
      (fun x => deriv gaussA (gaugeP1 x)*gaugeK1 x) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Ioo (0:ℝ) (1/8) from ⟨hz,hz1⟩)] with x hx
    exact (gaugeY1_hasDerivAt x hx.1 hx.2).deriv
  rw [(hd.congr_of_eventuallyEq he).deriv]
  simp only [Function.comp_apply]
  ring

theorem gaugeY2_second_deriv (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    deriv (deriv gaugeY2) z =
      deriv (deriv gaussA) (gaugeP2 z)*gaugeK2 z^2+
        deriv gaussA (gaugeP2 z)*(gaugeK2 z*gaugeT 256 z) := by
  have ha := (gaussA_analyticAt (gaugeP2 z) (gaugeP2_norm_lt_one z hz hz1)).deriv.differentiableAt.hasDerivAt
  have hd := (ha.comp z (gaugeP2_hasDerivAt z (by positivity) (by positivity))).mul
    (gaugeK2_hasDerivAt z (by positivity) (by positivity))
  have he : deriv gaugeY2 =ᶠ[nhds z]
      (fun x => deriv gaussA (gaugeP2 x)*gaugeK2 x) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Ioo (0:ℝ) (1/8) from ⟨hz,hz1⟩)] with x hx
    exact (gaugeY2_hasDerivAt x hx.1 hx.2).deriv
  rw [(hd.congr_of_eventuallyEq he).deriv]
  simp only [Function.comp_apply]
  ring

theorem theta_second_eq {f : ℝ → ℝ} {z : ℝ} (hf : AnalyticAt ℝ f z) :
    nativeTheta (nativeTheta f) z = z*deriv f z+z^2*deriv (deriv f) z := by
  have hd := (hasDerivAt_id z).mul hf.deriv.differentiableAt.hasDerivAt
  change z*deriv (fun x => x*deriv f x) z = _
  have he : deriv (fun x => x*deriv f x) z = deriv f z+z*deriv (deriv f) z := by
    convert! hd.deriv using 1
    simp only [id_eq, one_mul]
  rw [he]
  ring

theorem gaugeY1_equation (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    nativeTheta (nativeTheta gaugeY1) z+gaugeB1 z*nativeTheta gaugeY1 z+
      gaugeC1 z*gaugeY1 z = 0 := by
  have hp : gaugeP1 z*(1-gaugeP1 z) ≠ 0 := by
    rw [gaugeP1_product z (by positivity) (by positivity)]
    positivity
  have he := gaussA_equation (gaugeP1 z) (gaugeP1_norm_lt_one z hz hz1)
  have hl := gaugeP1_pullback_first z hz hz1
  have hc := gaugeP1_pullback_constant z hz
  apply (mul_eq_zero.mp (show gaugeP1 z*(1-gaugeP1 z)*
      (nativeTheta (nativeTheta gaugeY1) z+gaugeB1 z*nativeTheta gaugeY1 z+
        gaugeC1 z*gaugeY1 z) = 0 from ?_)).resolve_left hp
  rw [theta_second_eq (gaugeY1_analyticAt z hz hz1), nativeTheta,
    (gaugeY1_hasDerivAt z hz hz1).deriv, gaugeY1_second_deriv z hz hz1]
  dsimp only [gaugeY1]
  linear_combination (z^2*gaugeK1 z^2)*he+
    deriv gaussA (gaugeP1 z)*hl+gaussA (gaugeP1 z)*hc

theorem gaugeY2_equation (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    nativeTheta (nativeTheta gaugeY2) z+gaugeB2 z*nativeTheta gaugeY2 z+
      gaugeC2 z*gaugeY2 z = 0 := by
  have hp : gaugeP2 z*(1-gaugeP2 z) ≠ 0 := by
    rw [gaugeP2_product z (by positivity) (by positivity)]
    positivity
  have he := gaussA_equation (gaugeP2 z) (gaugeP2_norm_lt_one z hz hz1)
  have hl := gaugeP2_pullback_first z hz hz1
  have hc := gaugeP2_pullback_constant z hz
  apply (mul_eq_zero.mp (show gaugeP2 z*(1-gaugeP2 z)*
      (nativeTheta (nativeTheta gaugeY2) z+gaugeB2 z*nativeTheta gaugeY2 z+
        gaugeC2 z*gaugeY2 z) = 0 from ?_)).resolve_left hp
  rw [theta_second_eq (gaugeY2_analyticAt z hz hz1), nativeTheta,
    (gaugeY2_hasDerivAt z hz hz1).deriv, gaugeY2_second_deriv z hz hz1]
  dsimp only [gaugeY2]
  linear_combination (z^2*gaugeK2 z^2)*he+
    deriv gaussA (gaugeP2 z)*hl+gaussA (gaugeP2 z)*hc

end Row12GaussGauge

#print axioms Row12GaussGauge.gaugeK1_sq
#print axioms Row12GaussGauge.gaugeK2_sq
#print axioms Row12GaussGauge.gaugeP1_product
#print axioms Row12GaussGauge.gaugeP2_product
#print axioms Row12GaussGauge.gaugeP1_pullback_first
#print axioms Row12GaussGauge.gaugeP2_pullback_first
#print axioms Row12GaussGauge.gaugeP1_pullback_constant
#print axioms Row12GaussGauge.gaugeP2_pullback_constant
#print axioms Row12GaussGauge.gaugeY1_hasDerivAt
#print axioms Row12GaussGauge.gaugeY2_hasDerivAt
#print axioms Row12GaussGauge.gaugeY1_second_deriv
#print axioms Row12GaussGauge.gaugeY2_second_deriv
#print axioms Row12GaussGauge.theta_second_eq
#print axioms Row12GaussGauge.gaugeY1_equation
#print axioms Row12GaussGauge.gaugeY2_equation
