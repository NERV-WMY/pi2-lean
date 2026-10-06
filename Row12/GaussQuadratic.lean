import Row12.GaussSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Filter

namespace Row12

noncomputable def gaussP (q : ℝ) : ℝ := (1 - Real.sqrt (1 - q)) / 2

noncomputable def gaussG (q : ℝ) : ℝ := gaussA (gaussP q)

theorem gaussP_norm_lt_one (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    ‖gaussP q‖ < 1 := by
  have hs0 : 0 < Real.sqrt (1 - q) := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hs3 : Real.sqrt (1 - q) < 3 := by nlinarith
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> dsimp [gaussP] <;> linarith

theorem gaussP_zero : gaussP 0 = 0 := by norm_num [gaussP]

theorem gaussG_zero : gaussG 0 = 1 := by
  simp only [gaussG, gaussP_zero, gaussA_zero]

theorem gaussSqrt_hasDerivAt (q : ℝ) (hq : q < 1) :
    HasDerivAt (fun x : ℝ => Real.sqrt (1 - x))
      (-1 / (2 * Real.sqrt (1 - q))) q := by
  simpa only [zero_sub, id_eq] using
    ((hasDerivAt_id q).const_sub 1).sqrt (by linarith : 1 - q ≠ 0)

theorem gaussP_hasDerivAt (q : ℝ) (hq : q < 1) :
    HasDerivAt gaussP (1 / (4 * Real.sqrt (1 - q))) q := by
  have hs : Real.sqrt (1 - q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hd := ((gaussSqrt_hasDerivAt q hq).const_sub 1).div_const 2
  have he : -(-1 / (2 * Real.sqrt (1 - q))) / 2 =
      1 / (4 * Real.sqrt (1 - q)) := by field_simp [hs]; ring
  convert! hd.congr_deriv he using 1

theorem gaussSqrt_analyticAt (q : ℝ) (hq : q < 1) :
    AnalyticAt ℝ (fun x : ℝ => Real.sqrt (1 - x)) q := by
  have hl : AnalyticAt ℝ (fun x : ℝ => Real.log (1 - x)) q :=
    (analyticAt_log (by linarith : 0 < 1 - q)).comp (by fun_prop)
  have hh : AnalyticAt ℝ (fun x : ℝ => Real.log (1 - x) * (1 / 2)) q := by fun_prop
  have ha : AnalyticAt ℝ (fun x : ℝ => Real.exp (Real.log (1 - x) * (1 / 2))) q := hh.rexp'
  apply ha.congr
  have hn : Set.Iio (1 : ℝ) ∈ nhds q := isOpen_Iio.mem_nhds hq
  filter_upwards [hn] with x hx
  change x < 1 at hx
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : 0 < 1 - x)]

theorem gaussP_analyticAt (q : ℝ) (hq : q < 1) : AnalyticAt ℝ gaussP q := by
  have hs := gaussSqrt_analyticAt q hq
  unfold gaussP
  fun_prop

theorem gaussG_analyticAt (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    AnalyticAt ℝ gaussG q :=
  (gaussA_analyticAt (gaussP q) (gaussP_norm_lt_one q hq0 hq1)).comp
    (gaussP_analyticAt q hq1)

theorem gaussG_hasDerivAt (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    HasDerivAt gaussG
      (deriv gaussA (gaussP q) / (4 * Real.sqrt (1 - q))) q := by
  have ha := (gaussA_analyticAt (gaussP q)
    (gaussP_norm_lt_one q hq0 hq1)).differentiableAt.hasDerivAt
  have hd := ha.comp q (gaussP_hasDerivAt q hq1)
  have he : deriv gaussA (gaussP q) * (1 / (4 * Real.sqrt (1 - q))) =
      deriv gaussA (gaussP q) / (4 * Real.sqrt (1 - q)) := by ring
  convert! hd.congr_deriv he using 1

theorem gaussG_deriv (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    deriv gaussG q = deriv gaussA (gaussP q) / (4 * Real.sqrt (1 - q)) :=
  (gaussG_hasDerivAt q hq0 hq1).deriv

theorem gaussInvSqrt_hasDerivAt (q : ℝ) (hq : q < 1) :
    HasDerivAt (fun x : ℝ => 1 / (4 * Real.sqrt (1 - x)))
      (1 / (8 * Real.sqrt (1 - q) ^ 3)) q := by
  have hs : Real.sqrt (1 - q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hd := ((gaussSqrt_hasDerivAt q hq).const_mul 4).inv (mul_ne_zero (by norm_num) hs)
  have he : -(4 * (-1 / (2 * Real.sqrt (1 - q)))) / (4 * Real.sqrt (1 - q)) ^ 2 =
      1 / (8 * Real.sqrt (1 - q) ^ 3) := by field_simp [hs]; ring
  convert! hd.congr_deriv he using 1
  funext x
  exact one_div (4 * Real.sqrt (1 - x))

theorem gaussG_second_deriv (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    deriv (deriv gaussG) q =
      deriv (deriv gaussA) (gaussP q) / (16 * Real.sqrt (1 - q) ^ 2) +
      deriv gaussA (gaussP q) / (8 * Real.sqrt (1 - q) ^ 3) := by
  have hs : Real.sqrt (1 - q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have ha := (gaussA_analyticAt (gaussP q)
    (gaussP_norm_lt_one q hq0 hq1)).deriv.differentiableAt.hasDerivAt
  have hd := ((ha.comp q (gaussP_hasDerivAt q hq1)).mul
    (gaussInvSqrt_hasDerivAt q hq1))
  have he : deriv gaussG =ᶠ[nhds q]
      (fun x : ℝ => deriv gaussA (gaussP x) * (1 / (4 * Real.sqrt (1 - x)))) := by
    have hn : Set.Ioo (-8 : ℝ) 1 ∈ nhds q := isOpen_Ioo.mem_nhds ⟨hq0, hq1⟩
    filter_upwards [hn] with x hx
    rw [gaussG_deriv x hx.1 hx.2]
    ring
  rw [(hd.congr_of_eventuallyEq he).deriv]
  simp only [Function.comp_apply]
  field_simp [hs]
  ring

theorem gaussP_quadratic (q : ℝ) (hq : q < 1) :
    gaussP q * (1 - gaussP q) = q / 4 := by
  have hs : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  dsimp [gaussP]
  nlinarith

theorem gaussP_linear (q : ℝ) : 1 - 2 * gaussP q = Real.sqrt (1 - q) := by
  dsimp [gaussP]
  ring

theorem gaussG_equation (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    q * (1 - q) * deriv (deriv gaussG) q +
      (1 - 3 * q / 2) * deriv gaussG q - (5 / 144 : ℝ) * gaussG q = 0 := by
  have hs0 : Real.sqrt (1 - q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hs2 : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have he := gaussA_equation (gaussP q) (gaussP_norm_lt_one q hq0 hq1)
  rw [gaussP_quadratic q hq1, gaussP_linear q] at he
  rw [gaussG_second_deriv q hq0 hq1, gaussG_deriv q hq0 hq1]
  dsimp only [gaussG]
  have hid :
      q * (1 - q) * (deriv (deriv gaussA) (gaussP q) / (16 * Real.sqrt (1 - q) ^ 2) +
        deriv gaussA (gaussP q) / (8 * Real.sqrt (1 - q) ^ 3)) +
        (1 - 3 * q / 2) * (deriv gaussA (gaussP q) / (4 * Real.sqrt (1 - q))) -
        (5 / 144 : ℝ) * gaussA (gaussP q) =
      (q / 4 * deriv (deriv gaussA) (gaussP q) +
        Real.sqrt (1 - q) * deriv gaussA (gaussP q) - 5 / 36 * gaussA (gaussP q)) / 4 := by
    generalize Real.sqrt (1 - q) = s at hs0 hs2 ⊢
    have hq : q = 1 - s ^ 2 := by linarith
    rw [hq]
    field_simp [hs0]
    ring
  rw [hid, he]
  norm_num

theorem gaussG_theta_second (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    nativeTheta (nativeTheta gaussG) q =
      q * deriv gaussG q + q ^ 2 * deriv (deriv gaussG) q := by
  have hg := (gaussG_analyticAt q hq0 hq1).deriv.differentiableAt.hasDerivAt
  have hd := (hasDerivAt_id q).mul hg
  change q * deriv (fun x : ℝ => x * deriv gaussG x) q = _
  have he : deriv (fun x : ℝ => x * deriv gaussG x) q =
      deriv gaussG q + q * deriv (deriv gaussG) q := by
    convert! hd.deriv using 1
    simp only [id_eq, one_mul]
  rw [he]
  ring

theorem gaussG_nativeSecond (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    144 * (1 - q) * nativeTheta (nativeTheta gaussG) q -
      72 * q * nativeTheta gaussG q - 5 * q * gaussG q = 0 := by
  rw [gaussG_theta_second q hq0 hq1]
  dsimp only [nativeTheta]
  linear_combination 144 * q * gaussG_equation q hq0 hq1

end Row12

#print axioms Row12.gaussP_norm_lt_one
#print axioms Row12.gaussP_zero
#print axioms Row12.gaussG_zero
#print axioms Row12.gaussSqrt_hasDerivAt
#print axioms Row12.gaussP_hasDerivAt
#print axioms Row12.gaussSqrt_analyticAt
#print axioms Row12.gaussP_analyticAt
#print axioms Row12.gaussG_analyticAt
#print axioms Row12.gaussG_hasDerivAt
#print axioms Row12.gaussG_deriv
#print axioms Row12.gaussInvSqrt_hasDerivAt
#print axioms Row12.gaussG_second_deriv
#print axioms Row12.gaussP_quadratic
#print axioms Row12.gaussP_linear
#print axioms Row12.gaussG_equation
#print axioms Row12.gaussG_theta_second
#print axioms Row12.gaussG_nativeSecond
