import Row12.BetaPoles
import Row12.DualFrame
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace Row12

section BetaFrame



noncomputable def betaFrameRho : ℂ := 729/15625
noncomputable def betaFrameX (U : ℂ) : ℂ := 1-U^2
noncomputable def betaFrameLambda (x : ℂ) : ℂ := betaFrameRho*x^3
noncomputable def betaFrameM (x : ℂ) : ℂ := 25-9*x
noncomputable def betaFrameMid (x : ℂ) : ℂ := 27*x*(80-99*x+27*x^2)/1000
noncomputable def betaFrameMidX (x : ℂ) : ℂ := 27*(80-198*x+81*x^2)/1000
noncomputable def betaFrameEll (x : ℂ) : ℂ := 27*x*(9*x-16)/1000
noncomputable def betaFrameEllX (x : ℂ) : ℂ := 27*(18*x-16)/1000
noncomputable def betaFrameDenom (x : ℂ) : ℂ := x^4*betaFrameM x*(99*x-50)^2
noncomputable def betaFrameF (x s : ℂ) : ℂ := s^2-2*betaFrameMid x*s+betaFrameLambda x
noncomputable def betaFrameFX (x s : ℂ) : ℂ := -2*betaFrameMidX x*s+3*betaFrameRho*x^2
noncomputable def betaFrameH (U s : ℂ) : ℂ :=
  betaFrameDenom (betaFrameX U)*betaFrameF (betaFrameX U) s
noncomputable def betaFrameLambdaU (U : ℂ) : ℂ :=
  -6*betaFrameRho*U*(betaFrameX U)^2
noncomputable def betaFrameB (U s : ℂ) : ℂ := betaFrameLambda (betaFrameX U)/s

noncomputable def betaFrameLP (x : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let a := -1953125*(9*x-25)*(81*x^2-198*x+80)*(243*x^3-1053*x^2+1266*x-400)/209952
  let b := 244140625*(9*x-25)*(81*x^2-198*x+80)/944784
  !![0,0,a; 0,0,b; -a,-b,0]

noncomputable def betaFrameRP (x : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let a := 1953125*(59049*x^6-511758*x^5+1724085*x^4-2860596*x^3+
    2441988*x^2-1011200*x+160000)/209952
  let b := -244140625*(243*x^3-1053*x^2+1266*x-400)/944784
  !![0,0,a; 0,3906250*x*(99*x-50)/6561,b; a,b,30517578125/8503056]

noncomputable def scalarBetaSChart (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  (2*betaFrameLP x i j*(s-betaFrameMid x)+
    2*betaFrameEll x*betaFrameM x*betaFrameRP x i j)/
    (betaFrameDenom x*betaFrameF x s)

noncomputable def scalarBetaS (U s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  scalarBetaSChart (betaFrameX U) s

noncomputable def scalarBetaSFull (U s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  U • scalarBetaS U s

noncomputable def scalarBetaUChart (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  (-2*(1-x)*betaFrameLP x i j*betaFrameFX x s-
    2*betaFrameRP x i j*(-2*(1-x)*betaFrameEll x*betaFrameM x*betaFrameMidX x+
      (s-betaFrameMid x)*((betaFrameEll x-2*(1-x)*betaFrameEllX x)*betaFrameM x+
        9*(1-x)*betaFrameEll x)))/(betaFrameDenom x*betaFrameF x s)

noncomputable def scalarBetaU (U s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  scalarBetaUChart (betaFrameX U) s

noncomputable def betaPartialU (B : ℂ → ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (U s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j => deriv (fun V => B V s i j) U

noncomputable def betaPartialS (B : ℂ → ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (U s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j => deriv (fun z => B U z i j) s

noncomputable def betaCovariantU (B : ℂ → ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (U s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  betaPartialU B U s-(betaFrameLambdaU U/s) •
    (B U s*(ordinarySymmetricConnection (betaFrameB U s)).transpose)

noncomputable def betaCovariantS (B : ℂ → ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (U s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  betaPartialS B U s-ordinarySymmetricConnection s*B U s+
    (betaFrameLambda (betaFrameX U)/s^2) •
      (B U s*(ordinarySymmetricConnection (betaFrameB U s)).transpose)

noncomputable def scalarBetaSource (U s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  -betaCovariantU scalarBetaSFull U s+betaCovariantS scalarBetaU U s

noncomputable def betaPair (B : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, v i*B i j*w j

theorem betaFrame_real_agreement (x : ℝ) :
    betaFrameLP (x : ℂ)=(scalarLP x).map Complex.ofReal ∧
    betaFrameRP (x : ℂ)=(scalarRP x).map Complex.ofReal ∧
    betaFrameM (x : ℂ)=(scalarM x : ℂ) ∧ betaFrameMid (x : ℂ)=(scalarMid x : ℂ) ∧
    betaFrameEll (x : ℂ)=(scalarEll x : ℂ) ∧ betaFrameDenom (x : ℂ)=(scalarDenom x : ℂ) ∧
    betaFrameLambda (x : ℂ)=(scalarLambda x : ℂ) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [betaFrameLP, scalarLP, Matrix.map_apply]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [betaFrameRP, scalarRP, Matrix.map_apply]
  simp [betaFrameM, scalarM, betaFrameMid, scalarMid, betaFrameEll, scalarEll,
    betaFrameDenom, scalarDenom, betaFrameLambda, scalarLambda, betaFrameRho, rho]

theorem betaFrameMid_hasDerivAt (x : ℂ) :
    HasDerivAt betaFrameMid (betaFrameMidX x) x := by
  have h := ((((hasDerivAt_id x).const_mul (80 : ℂ)).fun_sub
    (((hasDerivAt_id x).fun_pow 2).const_mul (99 : ℂ))).fun_add
      (((hasDerivAt_id x).fun_pow 3).const_mul (27 : ℂ))).const_mul (27/1000 : ℂ)
  have heq : betaFrameMid = (fun y : ℂ => (27/1000)*(80*y-99*y^2+27*y^3)) := by
    funext z
    simp only [betaFrameMid]
    ring
  rw [heq]
  exact h.congr_deriv (by norm_num [betaFrameMidX]; ring)

theorem betaFrameEll_hasDerivAt (x : ℂ) :
    HasDerivAt betaFrameEll (betaFrameEllX x) x := by
  have h := ((((hasDerivAt_id x).fun_pow 2).const_mul (9 : ℂ)).fun_sub
    ((hasDerivAt_id x).const_mul (16 : ℂ))).const_mul (27/1000 : ℂ)
  have heq : betaFrameEll = (fun y : ℂ => (27/1000)*(9*y^2-16*y)) := by
    funext z
    simp only [betaFrameEll]
    ring
  rw [heq]
  exact h.congr_deriv (by norm_num [betaFrameEllX]; ring)

theorem betaFrameX_hasDerivAt (U : ℂ) : HasDerivAt betaFrameX (-2*U) U := by
  unfold betaFrameX
  exact ((hasDerivAt_const U (1 : ℂ)).fun_sub ((hasDerivAt_id U).fun_pow 2)).congr_deriv
    (by norm_num)

theorem betaFrameLambda_path_hasDerivAt (U : ℂ) :
    HasDerivAt (fun V => betaFrameLambda (betaFrameX V)) (betaFrameLambdaU U) U := by
  have h := ((betaFrameX_hasDerivAt U).fun_pow 3).const_mul (betaFrameRho : ℂ)
  change HasDerivAt (fun V => betaFrameRho*(betaFrameX V)^3) (betaFrameLambdaU U) U
  exact h.congr_deriv (by norm_num [betaFrameLambdaU]; ring)

theorem betaFrameF_hasDerivAt_x (x s : ℂ) :
    HasDerivAt (fun z => betaFrameF z s) (betaFrameFX x s) x := by
  have h := ((hasDerivAt_const x (s^2)).fun_sub
    ((betaFrameMid_hasDerivAt x).const_mul (2*s))).fun_add
      (((hasDerivAt_id x).fun_pow 3).const_mul betaFrameRho)
  have heq : (fun z : ℂ => betaFrameF z s) =
      (fun z : ℂ => s^2-2*s*betaFrameMid z+betaFrameRho*z^3) := by
    funext z
    simp only [betaFrameF, betaFrameLambda]
    ring
  rw [heq]
  exact h.congr_deriv (by norm_num [betaFrameFX]; ring)

theorem scalarBetaU_frozen_recipe (U s : ℂ) (i j : Fin 3) :
    scalarBetaU U s i j =
      (U*betaFrameLP (betaFrameX U) i j*(betaFrameFX (betaFrameX U) s*(-2*U))-
        2*betaFrameRP (betaFrameX U) i j*
          ((U*betaFrameEll (betaFrameX U))*betaFrameM (betaFrameX U)*
            (betaFrameMidX (betaFrameX U)*(-2*U))+
            (s-betaFrameMid (betaFrameX U))*
              ((betaFrameEll (betaFrameX U)-2*U^2*betaFrameEllX (betaFrameX U))*
                betaFrameM (betaFrameX U)+9*U*(U*betaFrameEll (betaFrameX U)))))/
        betaFrameH U s := by
  unfold scalarBetaU scalarBetaUChart betaFrameH
  rw [show 1-betaFrameX U=U^2 by unfold betaFrameX; ring]
  congr 1
  ring

theorem betaFrameB_hasDerivAt_U (U s : ℂ) :
    HasDerivAt (fun V => betaFrameB V s) (betaFrameLambdaU U/s) U := by
  simpa [betaFrameB] using (betaFrameLambda_path_hasDerivAt U).div_const s

theorem betaFrameB_hasDerivAt_s (U s : ℂ) (hs : s ≠ 0) :
    HasDerivAt (betaFrameB U) (-betaFrameLambda (betaFrameX U)/s^2) s := by
  unfold betaFrameB
  exact ((hasDerivAt_const s (betaFrameLambda (betaFrameX U))).fun_div
    (hasDerivAt_id s) hs).congr_deriv (by simp)

@[fun_prop] theorem betaFrameLP_differentiableAt (x : ℂ) (i j : Fin 3) :
    DifferentiableAt ℂ (fun z => betaFrameLP z i j) x := by
  fin_cases i <;> fin_cases j <;> simp [betaFrameLP] <;> fun_prop

@[fun_prop] theorem betaFrameRP_differentiableAt (x : ℂ) (i j : Fin 3) :
    DifferentiableAt ℂ (fun z => betaFrameRP z i j) x := by
  fin_cases i <;> fin_cases j <;> simp [betaFrameRP] <;> fun_prop

theorem scalarBetaSChart_differentiableAt_x (x s : ℂ)
    (hH : betaFrameDenom x*betaFrameF x s ≠ 0) (i j : Fin 3) :
    DifferentiableAt ℂ (fun z => scalarBetaSChart z s i j) x := by
  unfold scalarBetaSChart
  apply DifferentiableAt.div
  · unfold betaFrameMid betaFrameEll betaFrameM
    fun_prop
  · unfold betaFrameDenom betaFrameM betaFrameF betaFrameMid betaFrameLambda
    fun_prop
  · exact hH

theorem scalarBetaSFull_entry_hasDerivAt_U (U s : ℂ) (hH : betaFrameH U s ≠ 0)
    (i j : Fin 3) : HasDerivAt (fun V => scalarBetaSFull V s i j)
      (betaPartialU scalarBetaSFull U s i j) U := by
  apply DifferentiableAt.hasDerivAt
  have hc := (scalarBetaSChart_differentiableAt_x (betaFrameX U) s hH i j).comp U
    (betaFrameX_hasDerivAt U).differentiableAt
  convert differentiableAt_id.mul hc using 1 <;> rfl

theorem scalarBetaU_entry_hasDerivAt_s (U s : ℂ) (hH : betaFrameH U s ≠ 0)
    (i j : Fin 3) : HasDerivAt (fun z => scalarBetaU U z i j)
      (betaPartialS scalarBetaU U s i j) s := by
  apply DifferentiableAt.hasDerivAt
  unfold scalarBetaU scalarBetaUChart
  apply DifferentiableAt.div
  · unfold betaFrameFX
    fun_prop
  · unfold betaFrameF
    fun_prop
  · exact hH

private theorem betaPair_hasDerivAt (B B' : ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (v v' w w' : ℂ → Fin 3 → ℂ) (z : ℂ)
    (hB : ∀ i j, HasDerivAt (fun y => B y i j) (B' z i j) z)
    (hv : HasDerivAt v (v' z) z) (hw : HasDerivAt w (w' z) z) :
    HasDerivAt (fun y => betaPair (B y) (v y) (w y))
      (betaPair (B' z) (v z) (w z)+betaPair (B z) (v' z) (w z)+
        betaPair (B z) (v z) (w' z)) z := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      (((hasDerivAt_pi.1 hv i).fun_mul (hB i j)).fun_mul (hasDerivAt_pi.1 hw j))))
  apply h.congr_deriv
  simp only [betaPair, add_mul, Finset.sum_add_distrib]
  ring

private theorem betaPair_add (A B : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) :
    betaPair (A+B) v w=betaPair A v w+betaPair B v w := by
  simp [betaPair, mul_add, add_mul, Finset.sum_add_distrib]

private theorem betaPair_neg (B : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) :
    betaPair (-B) v w= -betaPair B v w := by simp [betaPair]

private theorem betaPair_sub (A B : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) :
    betaPair (A-B) v w=betaPair A v w-betaPair B v w := by
  rw [sub_eq_add_neg, betaPair_add, betaPair_neg, sub_eq_add_neg]

private theorem betaPair_smul (c : ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) :
    betaPair (c • B) v w=c*betaPair B v w := by
  simp only [betaPair, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem betaPair_smul_right (c : ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ)
    (v w : Fin 3 → ℂ) : betaPair B v (c • w)=c*betaPair B v w := by
  simp only [betaPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem betaPair_neg_left (B : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) :
    betaPair B (-v) w= -betaPair B v w := by simp [betaPair]

private theorem betaPair_neg_right (B : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) :
    betaPair B v (-w)= -betaPair B v w := by simp [betaPair]

private theorem betaPair_zero_left (B : Matrix (Fin 3) (Fin 3) ℂ) (w : Fin 3 → ℂ) :
    betaPair B 0 w=0 := by simp [betaPair]

private theorem betaPair_connection_rules (A B : Matrix (Fin 3) (Fin 3) ℂ)
    (v w : Fin 3 → ℂ) :
    betaPair (A*B) v w=betaPair B (A.transpose.mulVec v) w ∧
    betaPair (B*A.transpose) v w=betaPair B v (A.transpose.mulVec w) := by
  constructor <;>
    simp [betaPair, Matrix.mul_apply, Matrix.mulVec, Matrix.transpose_apply,
      dotProduct, Fin.sum_univ_succ] <;> ring

theorem scalarBetaSFull_pair_factor (U s : ℂ) (v w : Fin 3 → ℂ) :
    betaPair (scalarBetaSFull U s) v w=U*betaPair (scalarBetaS U s) v w :=
  betaPair_smul U _ v w

theorem scalarBetaSFull_pair_hasDerivAt_U (U s : ℂ)
    (hH : betaFrameH U s ≠ 0) (hb : ‖betaFrameB U s‖ < 1) (hb0 : betaFrameB U s ≠ 0) :
    HasDerivAt (fun V => betaPair (scalarBetaSFull V s) (dualState s) (dualState (betaFrameB V s)))
      (betaPair (betaCovariantU scalarBetaSFull U s) (dualState s)
        (dualState (betaFrameB U s))) U := by
  have hw := (dual_state_hasDerivAt (betaFrameB U s) hb hb0).scomp U
    (betaFrameB_hasDerivAt_U U s)
  have h := betaPair_hasDerivAt (fun V => scalarBetaSFull V s)
    (fun V => betaPartialU scalarBetaSFull V s)
    (fun _ => dualState s) (fun _ => 0) (fun V => dualState (betaFrameB V s))
    (fun _ => (betaFrameLambdaU U/s) •
      (-((ordinarySymmetricConnection (betaFrameB U s)).transpose.mulVec
        (dualState (betaFrameB U s))))) U
    (scalarBetaSFull_entry_hasDerivAt_U U s hH) (hasDerivAt_const U _) hw
  apply h.congr_deriv
  rw [betaCovariantU, betaPair_sub, betaPair_smul,
    (betaPair_connection_rules _ _ _ _).2]
  simp only [betaPair_zero_left, betaPair_smul_right, betaPair_neg_right,
    mul_neg, add_zero, sub_eq_add_neg]

theorem scalarBetaU_pair_hasDerivAt_s (U s : ℂ) (hH : betaFrameH U s ≠ 0)
    (hs : ‖s‖ < 1) (hs0 : s ≠ 0) (hb : ‖betaFrameB U s‖ < 1) (hb0 : betaFrameB U s ≠ 0) :
    HasDerivAt (fun z => betaPair (scalarBetaU U z) (dualState z) (dualState (betaFrameB U z)))
      (betaPair (betaCovariantS scalarBetaU U s) (dualState s)
        (dualState (betaFrameB U s))) s := by
  have hv := dual_state_hasDerivAt s hs hs0
  have hw := (dual_state_hasDerivAt (betaFrameB U s) hb hb0).scomp s
    (betaFrameB_hasDerivAt_s U s hs0)
  have h := betaPair_hasDerivAt (scalarBetaU U) (fun z => betaPartialS scalarBetaU U z)
    dualState (fun _ => -((ordinarySymmetricConnection s).transpose.mulVec (dualState s)))
    (fun z => dualState (betaFrameB U z))
    (fun _ => (-betaFrameLambda (betaFrameX U)/s^2) •
      (-((ordinarySymmetricConnection (betaFrameB U s)).transpose.mulVec
        (dualState (betaFrameB U s))))) s
    (scalarBetaU_entry_hasDerivAt_s U s hH) hv hw
  apply h.congr_deriv
  rw [betaCovariantS, betaPair_add, betaPair_sub, betaPair_smul,
    (betaPair_connection_rules _ _ _ _).1, (betaPair_connection_rules _ _ _ _).2]
  simp only [betaPair_neg_left, betaPair_smul_right, betaPair_neg_right,
    neg_div, mul_neg, sub_eq_add_neg]
  ring

theorem scalarBetaSource_pair_identity (U s : ℂ) (hH : betaFrameH U s ≠ 0)
    (hs : ‖s‖ < 1) (hs0 : s ≠ 0) (hb : ‖betaFrameB U s‖ < 1) (hb0 : betaFrameB U s ≠ 0) :
    betaPair (scalarBetaSource U s) (dualState s) (dualState (betaFrameB U s)) =
      -deriv (fun V => betaPair (scalarBetaSFull V s) (dualState s)
        (dualState (betaFrameB V s))) U+
      deriv (fun z => betaPair (scalarBetaU U z) (dualState z)
        (dualState (betaFrameB U z))) s := by
  rw [(scalarBetaSFull_pair_hasDerivAt_U U s hH hb hb0).deriv,
    (scalarBetaU_pair_hasDerivAt_s U s hH hs hs0 hb hb0).deriv]
  exact (betaPair_add _ _ _ _).trans (by rw [betaPair_neg])

end BetaFrame

end Row12

#print axioms Row12.betaFrame_real_agreement
#print axioms Row12.betaFrameMid_hasDerivAt
#print axioms Row12.betaFrameEll_hasDerivAt
#print axioms Row12.betaFrameX_hasDerivAt
#print axioms Row12.betaFrameLambda_path_hasDerivAt
#print axioms Row12.betaFrameF_hasDerivAt_x
#print axioms Row12.scalarBetaU_frozen_recipe
#print axioms Row12.betaFrameB_hasDerivAt_U
#print axioms Row12.betaFrameB_hasDerivAt_s
#print axioms Row12.betaFrameLP_differentiableAt
#print axioms Row12.betaFrameRP_differentiableAt
#print axioms Row12.scalarBetaSChart_differentiableAt_x
#print axioms Row12.scalarBetaSFull_entry_hasDerivAt_U
#print axioms Row12.scalarBetaU_entry_hasDerivAt_s
#print axioms Row12.scalarBetaSFull_pair_factor
#print axioms Row12.scalarBetaSFull_pair_hasDerivAt_U
#print axioms Row12.scalarBetaU_pair_hasDerivAt_s
#print axioms Row12.scalarBetaSource_pair_identity
