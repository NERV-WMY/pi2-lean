import Row12EulerSupport.Substitution
import Row12EulerSupport.DominatedLimit
import Row12EulerSupport.FunctionBound
import Row12.GaussEulerIntegral

open Set Filter intervalIntegral Topology

namespace Row12EulerSupport

theorem gaussDerivative_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    deriv (Row12.gaussA : ℝ → ℝ) (1 - p) =
      (1 / (12 * Real.pi)) * (∫ x : ℝ in 0..1, derivativeKernel p x) := by
  rw [Row12.gaussA_deriv_eq_eulerIntegral (by linarith : 0 ≤ 1 - p)
    (by linarith : 1 - p < 1), ← integral_const_mul]
  apply integral_congr_Ioo_of_le zero_le_one
  intro x hx
  dsimp only
  have hxpow : x * x ^ (-1 / 6 : ℝ) = x ^ (5 / 6 : ℝ) := by
    rw [show (5 / 6 : ℝ) = 1 + (-1 / 6) by norm_num,
      Real.rpow_add hx.1, Real.rpow_one]
  rw [Row12.betaDensity_five_sixths]
  unfold derivativeKernel
  calc
    _ = (1 / (12 * Real.pi)) * (x * x ^ (-1 / 6 : ℝ)) *
        (1 - x) ^ (-5 / 6 : ℝ) * (1 - (1 - p) * x) ^ (-7 / 6 : ℝ) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ = _ := by rw [hxpow]; ring

theorem gaussDerivative_transformed {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    -p * deriv (Row12.gaussA : ℝ → ℝ) (1 - p) =
      -(1 / (12 * Real.pi)) * (∫ y : ℝ in 0..1, endpointIntegrand p y) := by
  rw [gaussDerivative_kernel hp hp1]
  calc
    _ = -(1 / (12 * Real.pi)) * (p * ∫ x : ℝ in 0..1, derivativeKernel p x) := by
      ring
    _ = _ := by
      rw [derivativeKernel_substitution hp hp1]
      rfl

theorem derivativeEndpoint :
    Tendsto (fun p : ℝ => -p * deriv (Row12.gaussA : ℝ → ℝ) (1 - p))
      (𝓝[Ioi 0] 0) (𝓝 (-1 / (2 * Real.pi))) := by
  have h := endpointIntegral_tendsto.const_mul (-(1 / (12 * Real.pi)))
  have he : -(1 / (12 * Real.pi)) * 6 = -1 / (2 * Real.pi) := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [he] at h
  apply h.congr'
  have hp : ∀ᶠ p : ℝ in 𝓝[Ioi 0] 0, 0 < p := self_mem_nhdsWithin
  have hp1 : ∀ᶠ p : ℝ in 𝓝[Ioi 0] 0, p < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp, hp1] with p hp hp1
  exact (gaussDerivative_transformed hp hp1).symm

theorem functionEndpoint :
    Tendsto (fun p : ℝ => p * Row12.gaussA (1 - p))
      (𝓝[Ioi 0] 0) (𝓝 0) := by
  apply functionIntegralEndpoint_tendsto.congr'
  have hp : ∀ᶠ p : ℝ in 𝓝[Ioi 0] 0, 0 < p := self_mem_nhdsWithin
  have hp1 : ∀ᶠ p : ℝ in 𝓝[Ioi 0] 0, p < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp, hp1] with p hp hp1
  rw [Row12.gaussA_eq_eulerIntegral (by linarith : 0 ≤ 1 - p)
    (by linarith : 1 - p < 1)]

end Row12EulerSupport

#print axioms Row12EulerSupport.gaussDerivative_kernel
#print axioms Row12EulerSupport.gaussDerivative_transformed
#print axioms Row12EulerSupport.derivativeEndpoint
#print axioms Row12EulerSupport.functionEndpoint
