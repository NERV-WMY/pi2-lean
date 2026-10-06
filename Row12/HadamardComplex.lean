import Row12.Hadamard

open MeasureTheory Set Metric Complex intervalIntegral
open scoped ENNReal NNReal

namespace Row12

noncomputable def hadamardComplexEulerIntegral (k : ℕ) (lambda : ℂ) (r : ℝ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ •
    ∮ s in C(0,r), nativeF s * nativeEuler k (lambda/s) / s

theorem hadamardComplexEuler_hasSum (k : ℕ) lambda {r : ℝ}
    (hr : 0 < r) (hlr : ‖lambda‖ < r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => (coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ k * lambda ^ n)
      (hadamardComplexEulerIntegral k lambda r) := by
  have ht0 : 0 ≤ ‖lambda‖ / r := div_nonneg (norm_nonneg lambda) hr.le
  have ht1 : ‖lambda‖ / r < 1 := (div_lt_one hr).2 hlr
  have hgeom : Summable (fun n : ℕ => (n : ℝ) ^ k * (‖lambda‖ / r) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg ht0] using ht1)
  have hFs : ContinuousOn (nativeF : ℂ → ℂ) (sphere 0 r) :=
    (nativeF_differentiableOn_closedBall hr1).continuousOn.mono sphere_subset_closedBall
  have hFint : CircleIntegrable (nativeF : ℂ → ℂ) 0 r := hFs.circleIntegrable hr.le
  have hsz (s : ℂ) (hs : s ∈ sphere 0 r) : s ≠ 0 := by
    have hsr : ‖s‖ = r := by simpa using (mem_sphere.mp hs)
    exact norm_ne_zero_iff.mp (hsr.symm ▸ hr.ne')
  let T : ℕ → ℂ → ℂ := fun n s =>
    (coefficient3 n : ℂ) * (n : ℂ) ^ k * (lambda / s) ^ n * (nativeF s / s)
  have hTint (n : ℕ) : CircleIntegrable (T n) 0 r := by
    have hd : ContinuousOn (fun s : ℂ => lambda / s) (sphere 0 r) :=
      continuousOn_const.div continuousOn_id hsz
    exact ((continuousOn_const.mul (hd.pow n)).mul
      (hFs.div continuousOn_id hsz)).circleIntegrable hr.le
  have hnq (theta : ℝ) : ‖lambda / circleMap 0 r theta‖ = ‖lambda‖ / r := by
    simp only [norm_div, norm_circleMap_zero, abs_of_pos hr]
  have hnorm (n : ℕ) (theta : ℝ) :
      ‖deriv (circleMap 0 r) theta • T n (circleMap 0 r theta)‖ =
        coefficient3 n * (n : ℝ) ^ k * (‖lambda‖ / r) ^ n *
          ‖nativeF (circleMap 0 r theta)‖ := by
    simp only [T, deriv_circleMap, norm_smul, norm_mul, norm_pow, norm_div,
      norm_circleMap_zero, abs_of_pos hr, norm_I, mul_one,
      Complex.norm_of_nonneg (coefficient3_nonneg n), RCLike.norm_natCast]
    field_simp [hr.ne']
  have hnormint : IntervalIntegrable
      (fun theta : ℝ => ‖nativeF (circleMap 0 r theta)‖) volume 0 (2 * Real.pi) := hFint.norm
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 2 * Real.pi) (μ := volume)
    (F := fun n theta => deriv (circleMap 0 r) theta • T n (circleMap 0 r theta))
    (f := fun theta => deriv (circleMap 0 r) theta •
      (nativeEuler k (lambda / circleMap 0 r theta) *
        (nativeF (circleMap 0 r theta) / circleMap 0 r theta)))
    (fun n theta => ‖nativeF (circleMap 0 r theta)‖ *
      ((n : ℝ) ^ k * (‖lambda‖ / r) ^ n))
    (fun n => (hTint n).out.aestronglyMeasurable_restrict_uIoc)
    (fun n => Filter.Eventually.of_forall (fun theta _ => by
      rw [hnorm]
      calc
        coefficient3 n * (n : ℝ) ^ k * (‖lambda‖ / r) ^ n *
            ‖nativeF (circleMap 0 r theta)‖ ≤
            1 * (n : ℝ) ^ k * (‖lambda‖ / r) ^ n *
              ‖nativeF (circleMap 0 r theta)‖ := by
          gcongr
          exact coefficient3_le_one n
        _ = _ := by ring))
    (Filter.Eventually.of_forall (fun theta _ =>
      hgeom.mul_left ‖nativeF (circleMap 0 r theta)‖))
    (by simpa only [tsum_mul_left] using
      hnormint.mul_const (∑' n : ℕ, (n : ℝ) ^ k * (‖lambda‖ / r) ^ n))
    (Filter.Eventually.of_forall (fun theta _ => by
      have hq : ‖lambda / circleMap 0 r theta‖ < 1 := by rwa [hnq]
      exact ((nativeEuler_summable k _ hq).hasSum.mul_right
        (nativeF (circleMap 0 r theta) / circleMap 0 r theta)).const_smul
          (deriv (circleMap 0 r) theta)))
  change HasSum (fun n : ℕ => ∮ s in C(0, r), T n s)
    (∮ s in C(0, r), nativeEuler k (lambda / s) * (nativeF s / s)) at hsum
  have hcoeff (n : ℕ) :
      (2 * Real.pi * I : ℂ)⁻¹ • (∮ s in C(0, r), T n s) =
        (coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ k * lambda ^ n := by
    have hterm : (∮ s in C(0, r), T n s) =
        ((coefficient3 n : ℂ) * (n : ℂ) ^ k) •
          ∮ s in C(0, r), (lambda / s) ^ n • s⁻¹ • nativeF s := by
      rw [← circleIntegral.integral_smul]
      apply circleIntegral.integral_congr hr.le
      intro s hs
      dsimp [T]
      simp only [div_eq_mul_inv]
      ring
    calc
      _ = ((coefficient3 n : ℂ) * (n : ℂ) ^ k) •
          cauchyPowerSeries (nativeF : ℂ → ℂ) 0 r n (fun _ => lambda) := by
        rw [hterm, cauchyPowerSeries_apply]
        simp only [sub_zero]
        exact smul_comm _ _ _
      _ = _ := by
        rw [nativeF_cauchyCoefficient hr hr1]
        simp only [smul_eq_mul]
        ring
  have hresult : HasSum
      (fun n : ℕ => (coefficient3 n : ℂ) ^ 2 * (n : ℂ) ^ k * lambda ^ n)
      ((2 * Real.pi * I : ℂ)⁻¹ •
        ∮ s in C(0, r), nativeEuler k (lambda / s) * (nativeF s / s)) := by
    apply (hsum.const_smul ((2 * Real.pi * I : ℂ)⁻¹)).congr_fun
    intro n
    exact (hcoeff n).symm
  have heq : (∮ s in C(0, r), nativeEuler k (lambda / s) * (nativeF s / s)) =
      ∮ s in C(0, r), nativeF s * nativeEuler k (lambda / s) / s := by
    apply circleIntegral.integral_congr hr.le
    intro s hs
    ring
  rw [heq] at hresult
  exact hresult


end Row12

#print axioms Row12.hadamardComplexEuler_hasSum

