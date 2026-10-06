import Row12.NativeSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Metric Complex intervalIntegral
open scoped ENNReal NNReal

namespace Row12

theorem nativeF_hasFPowerSeriesAt :
    HasFPowerSeriesAt (nativeF : ℂ → ℂ) (nativeSeries ℂ) 0 := by
  have hr : (0 : ℝ≥0∞) < (nativeSeries ℂ).radius :=
    lt_of_lt_of_le (by norm_num) nativeSeries_radius
  have hp := (nativeSeries ℂ).hasFPowerSeriesOnBall hr
  have hfun : (nativeSeries ℂ).sum = (nativeF : ℂ → ℂ) := by
    funext z
    rw [nativeF_eq_tsum]
    apply tsum_congr
    intro n
    simp [nativeSeries, smul_eq_mul, mul_comm]
  rw [hfun] at hp
  exact hp.hasFPowerSeriesAt

theorem nativeF_differentiableOn_closedBall {r : ℝ} (hr1 : r < 1) :
    DifferentiableOn ℂ (nativeF : ℂ → ℂ) (closedBall 0 r) := by
  intro z hz
  have hzr : ‖z‖ ≤ r := by simpa using (mem_closedBall.mp hz)
  exact (nativeF_analyticAt z (hzr.trans_lt hr1)).differentiableAt.differentiableWithinAt

theorem nativeF_cauchySeries_eq {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    cauchyPowerSeries (nativeF : ℂ → ℂ) 0 r = nativeSeries ℂ := by
  let R : ℝ≥0 := ⟨r, hr.le⟩
  have hd : DifferentiableOn ℂ (nativeF : ℂ → ℂ) (closedBall 0 (R : ℝ)) :=
    nativeF_differentiableOn_closedBall hr1
  have hp := (hd.hasFPowerSeriesOnBall (show 0 < R from hr)).hasFPowerSeriesAt
  exact hp.eq_formalMultilinearSeries nativeF_hasFPowerSeriesAt

theorem nativeF_cauchyCoefficient {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (n : ℕ) (w : ℂ) :
    cauchyPowerSeries (nativeF : ℂ → ℂ) 0 r n (fun _ => w) =
      (coefficient3 n : ℂ) * w ^ n := by
  rw [nativeF_cauchySeries_eq hr hr1]
  simp [nativeSeries, smul_eq_mul, mul_comm]

noncomputable def hadamardEulerIntegral (k : ℕ) (lambda r : ℝ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ •
    ∮ s in C(0, r), nativeF s * nativeEuler k ((lambda : ℂ) / s) / s

theorem hadamardEuler_hasSum (k : ℕ) {lambda r : ℝ}
    (hlambda : 0 < lambda) (hlr : lambda < r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => (coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ k * (lambda : ℂ) ^ n)
      (hadamardEulerIntegral k lambda r) := by
  have hr : 0 < r := hlambda.trans hlr
  have ht0 : 0 ≤ lambda / r := (div_pos hlambda hr).le
  have ht1 : lambda / r < 1 := (div_lt_one hr).2 hlr
  have hgeom : Summable (fun n : ℕ => (n : ℝ) ^ k * (lambda / r) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg ht0] using ht1)
  have hFs : ContinuousOn (nativeF : ℂ → ℂ) (sphere 0 r) :=
    (nativeF_differentiableOn_closedBall hr1).continuousOn.mono sphere_subset_closedBall
  have hFint : CircleIntegrable (nativeF : ℂ → ℂ) 0 r := hFs.circleIntegrable hr.le
  have hsz (s : ℂ) (hs : s ∈ sphere 0 r) : s ≠ 0 := by
    have hsr : ‖s‖ = r := by simpa using (mem_sphere.mp hs)
    exact norm_ne_zero_iff.mp (hsr.symm ▸ hr.ne')
  let T : ℕ → ℂ → ℂ := fun n s =>
    (coefficient3 n : ℂ) * (n : ℂ) ^ k * ((lambda : ℂ) / s) ^ n * (nativeF s / s)
  have hTint (n : ℕ) : CircleIntegrable (T n) 0 r := by
    have hd : ContinuousOn (fun s : ℂ => (lambda : ℂ) / s) (sphere 0 r) :=
      continuousOn_const.div continuousOn_id hsz
    exact ((continuousOn_const.mul (hd.pow n)).mul
      (hFs.div continuousOn_id hsz)).circleIntegrable hr.le
  have hnq (theta : ℝ) : ‖(lambda : ℂ) / circleMap 0 r theta‖ = lambda / r := by
    simp only [norm_div, Complex.norm_of_nonneg hlambda.le, norm_circleMap_zero, abs_of_pos hr]
  have hnorm (n : ℕ) (theta : ℝ) :
      ‖deriv (circleMap 0 r) theta • T n (circleMap 0 r theta)‖ =
        coefficient3 n * (n : ℝ) ^ k * (lambda / r) ^ n *
          ‖nativeF (circleMap 0 r theta)‖ := by
    simp only [T, deriv_circleMap, norm_smul, norm_mul, norm_pow, norm_div,
      norm_circleMap_zero, abs_of_pos hr, norm_I, mul_one,
      Complex.norm_of_nonneg (coefficient3_nonneg n), RCLike.norm_natCast,
      Complex.norm_of_nonneg hlambda.le]
    field_simp [hr.ne']
  have hnormint : IntervalIntegrable
      (fun theta : ℝ => ‖nativeF (circleMap 0 r theta)‖) volume 0 (2 * Real.pi) := hFint.norm
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 2 * Real.pi) (μ := volume)
    (F := fun n theta => deriv (circleMap 0 r) theta • T n (circleMap 0 r theta))
    (f := fun theta => deriv (circleMap 0 r) theta •
      (nativeEuler k ((lambda : ℂ) / circleMap 0 r theta) *
        (nativeF (circleMap 0 r theta) / circleMap 0 r theta)))
    (fun n theta => ‖nativeF (circleMap 0 r theta)‖ *
      ((n : ℝ) ^ k * (lambda / r) ^ n))
    (fun n => (hTint n).out.aestronglyMeasurable_restrict_uIoc)
    (fun n => Filter.Eventually.of_forall (fun theta _ => by
      rw [hnorm]
      calc
        coefficient3 n * (n : ℝ) ^ k * (lambda / r) ^ n *
            ‖nativeF (circleMap 0 r theta)‖ ≤
            1 * (n : ℝ) ^ k * (lambda / r) ^ n *
              ‖nativeF (circleMap 0 r theta)‖ := by
          gcongr
          exact coefficient3_le_one n
        _ = _ := by ring))
    (Filter.Eventually.of_forall (fun theta _ =>
      hgeom.mul_left ‖nativeF (circleMap 0 r theta)‖))
    (by simpa only [tsum_mul_left] using
      hnormint.mul_const (∑' n : ℕ, (n : ℝ) ^ k * (lambda / r) ^ n))
    (Filter.Eventually.of_forall (fun theta _ => by
      have hq : ‖(lambda : ℂ) / circleMap 0 r theta‖ < 1 := by rwa [hnq]
      exact ((nativeEuler_summable k _ hq).hasSum.mul_right
        (nativeF (circleMap 0 r theta) / circleMap 0 r theta)).const_smul
          (deriv (circleMap 0 r) theta)))
  change HasSum (fun n : ℕ => ∮ s in C(0, r), T n s)
    (∮ s in C(0, r), nativeEuler k ((lambda : ℂ) / s) * (nativeF s / s)) at hsum
  have hcoeff (n : ℕ) :
      (2 * Real.pi * I : ℂ)⁻¹ • (∮ s in C(0, r), T n s) =
        (coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ k * (lambda : ℂ) ^ n := by
    have hterm : (∮ s in C(0, r), T n s) =
        ((coefficient3 n : ℂ) * (n : ℂ) ^ k) •
          ∮ s in C(0, r), ((lambda : ℂ) / s) ^ n • s⁻¹ • nativeF s := by
      rw [← circleIntegral.integral_smul]
      apply circleIntegral.integral_congr hr.le
      intro s hs
      dsimp [T]
      simp only [div_eq_mul_inv]
      ring
    calc
      _ = ((coefficient3 n : ℂ) * (n : ℂ) ^ k) •
          cauchyPowerSeries (nativeF : ℂ → ℂ) 0 r n (fun _ => (lambda : ℂ)) := by
        rw [hterm, cauchyPowerSeries_apply]
        simp only [sub_zero]
        exact smul_comm _ _ _
      _ = _ := by
        rw [nativeF_cauchyCoefficient hr hr1]
        simp only [smul_eq_mul]
        ring
  have hresult : HasSum
      (fun n : ℕ => (coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ k * (lambda : ℂ) ^ n)
      ((2 * Real.pi * I : ℂ)⁻¹ •
        ∮ s in C(0, r), nativeEuler k ((lambda : ℂ) / s) * (nativeF s / s)) := by
    apply (hsum.const_smul ((2 * Real.pi * I : ℂ)⁻¹)).congr_fun
    intro n
    exact (hcoeff n).symm
  have heq : (∮ s in C(0, r), nativeEuler k ((lambda : ℂ) / s) * (nativeF s / s)) =
      ∮ s in C(0, r), nativeF s * nativeEuler k ((lambda : ℂ) / s) / s := by
    apply circleIntegral.integral_congr hr.le
    intro s hs
    ring
  rw [heq] at hresult
  exact hresult

theorem hadamard_hasSum {lambda r : ℝ}
    (hlambda : 0 < lambda) (hlr : lambda < r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => (coefficient3 n : ℂ) ^ 2 * (lambda : ℂ) ^ n)
      (hadamardEulerIntegral 0 lambda r) := by
  simpa only [pow_zero, mul_one] using hadamardEuler_hasSum 0 hlambda hlr hr1

theorem hadamard_tsum {lambda r : ℝ}
    (hlambda : 0 < lambda) (hlr : lambda < r) (hr1 : r < 1) :
    (∑' n : ℕ, (coefficient3 n : ℂ) ^ 2 * (lambda : ℂ) ^ n) =
      hadamardEulerIntegral 0 lambda r :=
  (hadamard_hasSum hlambda hlr hr1).tsum_eq

theorem hadamardEuler_radius_independent (k : ℕ) {lambda r r' : ℝ}
    (hlambda : 0 < lambda) (hlr : lambda < r) (hr1 : r < 1)
    (hlr' : lambda < r') (hr1' : r' < 1) :
    hadamardEulerIntegral k lambda r = hadamardEulerIntegral k lambda r' :=
  (hadamardEuler_hasSum k hlambda hlr hr1).unique
    (hadamardEuler_hasSum k hlambda hlr' hr1')

end Row12

#print axioms Row12.nativeF_hasFPowerSeriesAt
#print axioms Row12.nativeF_differentiableOn_closedBall
#print axioms Row12.nativeF_cauchySeries_eq
#print axioms Row12.nativeF_cauchyCoefficient
#print axioms Row12.hadamardEuler_hasSum
#print axioms Row12.hadamard_hasSum
#print axioms Row12.hadamard_tsum
#print axioms Row12.hadamardEuler_radius_independent
