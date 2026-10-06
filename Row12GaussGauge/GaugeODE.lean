import Row12GaussGauge.Pullback
import Row12GaussGauge.Factor

open Filter Set Row12

namespace Row12GaussGauge

noncomputable def gaugeW (z : ℝ) : ℝ := gaugeL z*gaugeY1 z

theorem gaugeW_zero : gaugeW 0 = 1 := by
  simp [gaugeW, gaugeL_zero, gaugeY1_zero]

theorem gaugeW_analyticAt_zero : AnalyticAt ℝ gaugeW 0 :=
  gaugeL_analyticAt_zero.mul gaugeY1_analyticAt_zero

theorem gaugeW_analyticAt (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    AnalyticAt ℝ gaugeW z :=
  (gaugeL_analyticAt z (by positivity) (by positivity)).mul
    (gaugeY1_analyticAt z hz hz1)

theorem gaugeW_equation (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    nativeTheta (nativeTheta gaugeW) z+gaugeB2 z*nativeTheta gaugeW z+
      gaugeC2 z*gaugeW z = 0 :=
  gaugeL_mul_euler_equation gaugeY1 z hz hz1 (gaugeY1_analyticAt z hz hz1)
    (gaugeY1_equation z hz hz1)

theorem gaugeY2_equation_eventually :
    (fun z => nativeTheta (nativeTheta gaugeY2) z+
      gaugeB2 z*nativeTheta gaugeY2 z+gaugeC2 z*gaugeY2 z)
        =ᶠ[nhdsWithin 0 (Ioi 0)] 0 := by
  have hn : ∀ᶠ q in nhds (0:ℝ), q < (1/8:ℝ) := isOpen_Iio.mem_nhds (by norm_num)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz1 hz
  exact gaugeY2_equation z hz hz1

theorem gaugeW_equation_eventually :
    (fun z => nativeTheta (nativeTheta gaugeW) z+
      gaugeB2 z*nativeTheta gaugeW z+gaugeC2 z*gaugeW z)
        =ᶠ[nhdsWithin 0 (Ioi 0)] 0 := by
  have hn : ∀ᶠ q in nhds (0:ℝ), q < (1/8:ℝ) := isOpen_Iio.mem_nhds (by norm_num)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz1 hz
  exact gaugeW_equation z hz hz1

end Row12GaussGauge

#print axioms Row12GaussGauge.gaugeW_zero
#print axioms Row12GaussGauge.gaugeW_analyticAt_zero
#print axioms Row12GaussGauge.gaugeW_analyticAt
#print axioms Row12GaussGauge.gaugeW_equation
#print axioms Row12GaussGauge.gaugeY2_equation_eventually
#print axioms Row12GaussGauge.gaugeW_equation_eventually
