import Row12.Residue
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Row12

noncomputable def scalarLambda (x : ℝ) : ℝ := rho*x^3
noncomputable def scalarM (x : ℝ) : ℝ := 25-9*x
noncomputable def scalarMid (x : ℝ) : ℝ := 27*x*(80-99*x+27*x^2)/1000
noncomputable def scalarEll (x : ℝ) : ℝ := 27*x*(9*x-16)/1000
noncomputable def scalarDenom (x : ℝ) : ℝ := x^4*scalarM x*(99*x-50)^2

noncomputable def scalarLP (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let a := -1953125*(9*x-25)*(81*x^2-198*x+80)*(243*x^3-1053*x^2+1266*x-400)/209952
  let b := 244140625*(9*x-25)*(81*x^2-198*x+80)/944784
  !![0,0,a; 0,0,b; -a,-b,0]

noncomputable def scalarRP (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let a := 1953125*(59049*x^6-511758*x^5+1724085*x^4-2860596*x^3+
    2441988*x^2-1011200*x+160000)/209952
  let b := -244140625*(243*x^3-1053*x^2+1266*x-400)/944784
  !![0,0,a; 0,3906250*x*(99*x-50)/6561,b; a,b,30517578125/8503056]

theorem scalar_discriminant (x : ℝ) :
    scalarMid x^2-scalarLambda x = (1-x)*scalarEll x^2*scalarM x := by
  norm_num only [scalarMid, scalarLambda, scalarEll, scalarM, rho]
  ring

theorem scalarMid_pos {x : ℝ} (hx : 0<x) (hx1 : x<1) : 0<scalarMid x := by
  have hp : 0<(1-x)*(72-27*x) := mul_pos (by linarith) (by linarith)
  have hh : 0<80-99*x+27*x^2 := by nlinarith
  exact div_pos (mul_pos (mul_pos (by norm_num) hx) hh) (by norm_num)

theorem scalarEll_neg {x : ℝ} (hx : 0<x) (hx1 : x<1) : scalarEll x<0 := by
  apply div_neg_of_neg_of_pos _ (by norm_num)
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hx) (by linarith)

theorem scalarM_pos {x : ℝ} (hx1 : x<1) : 0<scalarM x := by
  unfold scalarM
  linarith

theorem scalarLambda_pos {x : ℝ} (hx : 0<x) : 0<scalarLambda x := by
  exact mul_pos (by norm_num [rho]) (pow_pos hx 3)

noncomputable def scalarPathX (U : ℝ) : ℝ := 1-U^2
noncomputable def scalarPolePlus (U : ℝ) : ℝ :=
  scalarMid (scalarPathX U)+U*scalarEll (scalarPathX U)*Real.sqrt (scalarM (scalarPathX U))
noncomputable def scalarPoleMinus (U : ℝ) : ℝ :=
  scalarMid (scalarPathX U)-U*scalarEll (scalarPathX U)*Real.sqrt (scalarM (scalarPathX U))

theorem scalarPathX_mem {U : ℝ} (hU : 0<U) (hU1 : U<1) :
    0<scalarPathX U ∧ scalarPathX U<1 := by
  unfold scalarPathX
  constructor
  · nlinarith [sq_nonneg (1-U)]
  · nlinarith

theorem scalar_poles_product {U : ℝ} (hU : 0<U) (hU1 : U<1) :
    scalarPolePlus U*scalarPoleMinus U = scalarLambda (scalarPathX U) := by
  have hx := scalarPathX_mem hU hU1
  have hs := Real.sq_sqrt (scalarM_pos hx.2).le
  have hd := scalar_discriminant (scalarPathX U)
  rw [scalarPolePlus, scalarPoleMinus]
  calc
    _ = scalarMid (scalarPathX U)^2-U^2*scalarEll (scalarPathX U)^2*
        Real.sqrt (scalarM (scalarPathX U))^2 := by ring
    _ = scalarMid (scalarPathX U)^2-U^2*scalarEll (scalarPathX U)^2*scalarM (scalarPathX U) := by rw [hs]
    _ = scalarLambda (scalarPathX U) := by
      have hUx : U^2=1-scalarPathX U := by unfold scalarPathX; ring
      rw [hUx]
      linear_combination hd

theorem scalarPoleMinus_gt_radius {U : ℝ} (hU : 0<U) (hU1 : U<1) :
    Real.sqrt (scalarLambda (scalarPathX U))<scalarPoleMinus U := by
  have hx := scalarPathX_mem hU hU1
  have hm := scalarMid_pos hx.1 hx.2
  have he := scalarEll_neg hx.1 hx.2
  have hM := scalarM_pos hx.2
  have hl := scalarLambda_pos hx.1
  have hS := Real.sqrt_pos.2 hM
  have hd := scalar_discriminant (scalarPathX U)
  have hdiff : 0<scalarMid (scalarPathX U)^2-scalarLambda (scalarPathX U) := by
    rw [hd]
    exact mul_pos (mul_pos (by linarith) (sq_pos_of_ne_zero (ne_of_lt he))) hM
  have hs := Real.sq_sqrt hl.le
  have hr := Real.sqrt_nonneg (scalarLambda (scalarPathX U))
  have hmid : Real.sqrt (scalarLambda (scalarPathX U))<scalarMid (scalarPathX U) := by
    nlinarith
  have hneg : U*scalarEll (scalarPathX U)*Real.sqrt (scalarM (scalarPathX U))<0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hU he) hS
  unfold scalarPoleMinus
  linarith

theorem scalarPolePlus_pos_lt_radius {U : ℝ} (hU : 0<U) (hU1 : U<1) :
    0<scalarPolePlus U ∧ scalarPolePlus U<Real.sqrt (scalarLambda (scalarPathX U)) := by
  have hp := scalar_poles_product hU hU1
  have hm := scalarPoleMinus_gt_radius hU hU1
  have hx := scalarPathX_mem hU hU1
  have hl := scalarLambda_pos hx.1
  have hr := Real.sqrt_pos.2 hl
  have hs := Real.sq_sqrt hl.le
  have hmpos : 0<scalarPoleMinus U := lt_trans hr hm
  have hprodpos : 0<scalarPolePlus U*scalarPoleMinus U := by rw [hp]; exact hl
  have hpluspos : 0<scalarPolePlus U := (mul_pos_iff_of_pos_right hmpos).mp hprodpos
  constructor
  · exact hpluspos
  · nlinarith [mul_lt_mul_of_pos_left hm hpluspos]

theorem scalar_contact_poles : scalarPolePlus 0=27/125 ∧ scalarPoleMinus 0=27/125 := by
  norm_num [scalarPolePlus, scalarPoleMinus, scalarPathX, scalarMid]

theorem scalar_positive_contact_matrix :
    (4/scalarDenom 1) • scalarRP 1 = contactSourceMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [scalarDenom, scalarM, scalarRP, contactSourceMatrix]

end Row12

#print axioms Row12.scalar_discriminant
#print axioms Row12.scalarMid_pos
#print axioms Row12.scalarEll_neg
#print axioms Row12.scalarM_pos
#print axioms Row12.scalarLambda_pos
#print axioms Row12.scalarPathX_mem
#print axioms Row12.scalar_poles_product
#print axioms Row12.scalarPoleMinus_gt_radius
#print axioms Row12.scalarPolePlus_pos_lt_radius
#print axioms Row12.scalar_contact_poles
#print axioms Row12.scalar_positive_contact_matrix
