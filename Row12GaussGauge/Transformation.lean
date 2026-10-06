import Row12GaussGauge.GaugeODE
import Row12GaussGauge.HBridge
import Row12.AnalyticSecondUniqueness

open Filter Set Row12

namespace Row12GaussGauge

theorem gauge_normalized_eq_eventually : gaugeY2 =ᶠ[nhds 0] gaugeW := by
  apply normalized_regularSecond_eq_eventually (fun _ => 1) gaugeB2 gaugeC2
    continuousAt_const gaugeB2_continuousAt_zero gaugeC2_continuousAt_zero
    (by norm_num) gaugeB2_zero gaugeC2_zero
    gaugeY2_analyticAt_zero gaugeW_analyticAt_zero
  · rw [gaugeY2_zero, gaugeW_zero]
  · filter_upwards [gaugeY2_equation_eventually] with z hz
    simpa only [regularSecond, one_mul] using hz
  · filter_upwards [gaugeW_equation_eventually] with z hz
    simpa only [regularSecond, one_mul] using hz

theorem gauge_transformation (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    gaugeY2 z = gaugeL z*gaugeY1 z := by
  have hf : AnalyticOnNhd ℝ gaugeY2 (Ioo (0:ℝ) (1/8)) := by
    intro q hq
    exact gaugeY2_analyticAt q hq.1 hq.2
  have hg : AnalyticOnNhd ℝ gaugeW (Ioo (0:ℝ) (1/8)) := by
    intro q hq
    exact gaugeW_analyticAt q hq.1 hq.2
  have hn : ∀ᶠ q in nhds (0:ℝ), q < (1/8:ℝ) := isOpen_Iio.mem_nhds (by norm_num)
  have hlocal : ∀ᶠ q in nhdsWithin (0:ℝ) (Ioi 0),
      q ∈ Ioo (0:ℝ) (1/8) ∧ gaugeY2 =ᶠ[nhds q] gaugeW := by
    filter_upwards [self_mem_nhdsWithin, hn.filter_mono nhdsWithin_le_nhds,
      gauge_normalized_eq_eventually.eventuallyEq_nhds.filter_mono nhdsWithin_le_nhds]
      with q hq hq1 heq
    exact ⟨⟨hq,hq1⟩,heq⟩
  obtain ⟨q0,hq0,heq⟩ := hlocal.exists
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_Ioo hq0 heq ⟨hz,hz1⟩

theorem gauge_transformation_eventually (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    gaugeY2 =ᶠ[nhds z] gaugeW := by
  filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Ioo (0:ℝ) (1/8) from ⟨hz,hz1⟩)] with q hq
  exact gauge_transformation q hq.1 hq.2

theorem gauge_transformation_derivative (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    deriv gaussA (gaugeP2 z)*gaugeK2 z =
      gaugeL z*gaugeMu z*gaussA (gaugeP1 z)+
        gaugeL z*(deriv gaussA (gaugeP1 z)*gaugeK1 z) := by
  have hd := (gaugeL_hasDerivAt z (by positivity) (by positivity)).mul
    (gaugeY1_hasDerivAt z hz hz1)
  calc
    _ = deriv gaugeY2 z := (gaugeY2_hasDerivAt z hz hz1).deriv.symm
    _ = deriv gaugeW z := (gauge_transformation_eventually z hz hz1).deriv_eq
    _ = _ := hd.deriv

theorem signed_gauss_transformation (h : ℝ) (hh : 8 < h) :
    gaussA (hP2 h) = hL h*gaussA (hP1 h) := by
  have hh0 : 0 < h := by linarith
  have hz : 0 < 1/h := one_div_pos.mpr hh0
  have hz1 : 1/h < (1/8:ℝ) :=
    (one_div_lt_one_div hh0 (by norm_num : (0:ℝ) < 8)).mpr hh
  rw [hP2_eq_gauge h hh, hP1_eq_gauge h hh, hL_eq_gauge h hh]
  exact gauge_transformation (1/h) hz hz1

theorem signed_gauss_transformation_derivative (h : ℝ) (hh : 8 < h) :
    deriv (fun x => gaussA (hP2 x)) h =
      deriv (fun x => hL x*gaussA (hP1 x)) h := by
  have he : (fun x => gaussA (hP2 x)) =ᶠ[nhds h]
      (fun x => hL x*gaussA (hP1 x)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hh] with x hx
    exact signed_gauss_transformation x hx
  exact he.deriv_eq

end Row12GaussGauge

#print axioms Row12GaussGauge.gauge_normalized_eq_eventually
#print axioms Row12GaussGauge.gauge_transformation
#print axioms Row12GaussGauge.gauge_transformation_eventually
#print axioms Row12GaussGauge.gauge_transformation_derivative
#print axioms Row12GaussGauge.signed_gauss_transformation
#print axioms Row12GaussGauge.signed_gauss_transformation_derivative
