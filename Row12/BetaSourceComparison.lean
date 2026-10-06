import Row12.BetaFrame
import Row12.AngularSourceCertificate

namespace Row12

set_option maxRecDepth 8000

noncomputable def betaSourceLPX (x : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let p := 81*x^2-198*x+80
  let p' := 162*x-198
  let q := 243*x^3-1053*x^2+1266*x-400
  let q' := 729*x^2-2106*x+1266
  let a := -1953125*(9*p*q+(9*x-25)*p'*q+(9*x-25)*p*q')/209952
  let b := 244140625*(9*p+(9*x-25)*p')/944784
  !![0,0,a; 0,0,b; -a,-b,0]

noncomputable def betaSourceRPX (x : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let a := 1953125*(354294*x^5-2558790*x^4+6896340*x^3-8581788*x^2+
    4883976*x-1011200)/209952
  let b := -244140625*(729*x^2-2106*x+1266)/944784
  !![0,0,a; 0,3906250*(198*x-50)/6561,b; a,b,0]

noncomputable def betaSourceDX (x : ℂ) : ℂ :=
  4*x^3*betaFrameM x*(99*x-50)^2-9*x^4*(99*x-50)^2+
    198*x^4*betaFrameM x*(99*x-50)

noncomputable def betaSourceNS (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  2*betaFrameLP x i j*(s-betaFrameMid x)+2*betaFrameEll x*betaFrameM x*betaFrameRP x i j

noncomputable def betaSourceNSX (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  2*betaSourceLPX x i j*(s-betaFrameMid x)-2*betaFrameLP x i j*betaFrameMidX x+
    2*(betaFrameEllX x*betaFrameM x-9*betaFrameEll x)*betaFrameRP x i j+
    2*betaFrameEll x*betaFrameM x*betaSourceRPX x i j

noncomputable def betaSourceNU (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  -2*(1-x)*betaFrameLP x i j*betaFrameFX x s-
    2*betaFrameRP x i j*(-2*(1-x)*betaFrameEll x*betaFrameM x*betaFrameMidX x+
      (s-betaFrameMid x)*((betaFrameEll x-2*(1-x)*betaFrameEllX x)*betaFrameM x+
        9*(1-x)*betaFrameEll x))

noncomputable def betaSourceNUS (x : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  4*(1-x)*betaFrameLP x i j*betaFrameMidX x-
    2*betaFrameRP x i j*((betaFrameEll x-2*(1-x)*betaFrameEllX x)*betaFrameM x+
      9*(1-x)*betaFrameEll x)

noncomputable def betaSourceSX (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  (betaSourceNSX x s i j*(betaFrameDenom x*betaFrameF x s)-
    betaSourceNS x s i j*(betaSourceDX x*betaFrameF x s+betaFrameDenom x*betaFrameFX x s))/
      (betaFrameDenom x*betaFrameF x s)^2

noncomputable def betaSourceUS (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  (betaSourceNUS x i j*(betaFrameDenom x*betaFrameF x s)-
    betaSourceNU x s i j*(betaFrameDenom x*(2*s-2*betaFrameMid x)))/
      (betaFrameDenom x*betaFrameF x s)^2

theorem betaSourceLP_deriv (x : ℂ) (i j : Fin 3) :
    deriv (fun z => betaFrameLP z i j) x=betaSourceLPX x i j := by
  fin_cases i <;> fin_cases j <;>
    simp (disch := fun_prop) [betaFrameLP, betaSourceLPX, deriv_fun_mul,
      deriv_fun_sub, deriv_fun_pow, deriv_fun_add, deriv_div_const] <;> ring

theorem betaSourceRP_deriv (x : ℂ) (i j : Fin 3) :
    deriv (fun z => betaFrameRP z i j) x=betaSourceRPX x i j := by
  fin_cases i <;> fin_cases j <;>
    simp (disch := fun_prop) [betaFrameRP, betaSourceRPX, deriv_fun_mul,
      deriv_fun_sub, deriv_fun_pow, deriv_fun_add, deriv_div_const] <;> ring

theorem betaSourceDenom_hasDerivAt (x : ℂ) :
    HasDerivAt betaFrameDenom (betaSourceDX x) x := by
  have hm := ((hasDerivAt_const x (25 : ℂ)).fun_sub
    ((hasDerivAt_id x).const_mul (9 : ℂ)))
  have hl := ((hasDerivAt_id x).const_mul (99 : ℂ)).fun_sub (hasDerivAt_const x (50 : ℂ))
  have h := (((hasDerivAt_id x).fun_pow 4).fun_mul hm).fun_mul (hl.fun_pow 2)
  change HasDerivAt betaFrameDenom _ x at h
  exact h.congr_deriv (by norm_num [betaSourceDX, betaFrameM]; ring)

theorem betaSourceNS_hasDerivAt (x s : ℂ) (i j : Fin 3) :
    HasDerivAt (fun z => betaSourceNS z s i j) (betaSourceNSX x s i j) x := by
  have hl := (betaFrameLP_differentiableAt x i j).hasDerivAt
  rw [betaSourceLP_deriv] at hl
  have hr := (betaFrameRP_differentiableAt x i j).hasDerivAt
  rw [betaSourceRP_deriv] at hr
  have hm := (hasDerivAt_const x s).fun_sub (betaFrameMid_hasDerivAt x)
  have hM := (hasDerivAt_const x (25 : ℂ)).fun_sub
    ((hasDerivAt_id x).const_mul (9 : ℂ))
  have h := ((hl.const_mul (2 : ℂ)).fun_mul hm).fun_add
    ((((betaFrameEll_hasDerivAt x).const_mul (2 : ℂ)).fun_mul hM).fun_mul hr)
  change HasDerivAt (fun z => betaSourceNS z s i j) _ x at h
  exact h.congr_deriv (by norm_num [betaSourceNSX, betaFrameM]; ring)

theorem betaSourceNU_hasDerivAt (x s : ℂ) (i j : Fin 3) :
    HasDerivAt (fun z => betaSourceNU x z i j) (betaSourceNUS x i j) s := by
  have hfx := ((hasDerivAt_id s).const_mul (-2*betaFrameMidX x)).fun_add
    (hasDerivAt_const s (3*betaFrameRho*x^2))
  have hid := (hasDerivAt_id s).fun_sub (hasDerivAt_const s (betaFrameMid x))
  have hn := (hasDerivAt_const s
      (-2*(1-x)*betaFrameEll x*betaFrameM x*betaFrameMidX x)).fun_add
    (hid.mul_const ((betaFrameEll x-2*(1-x)*betaFrameEllX x)*betaFrameM x+
      9*(1-x)*betaFrameEll x))
  have h := (hfx.const_mul (-2*(1-x)*betaFrameLP x i j)).fun_sub
    (hn.const_mul (2*betaFrameRP x i j))
  change HasDerivAt (fun z => betaSourceNU x z i j) _ s at h
  exact h.congr_deriv (by norm_num [betaSourceNUS]; ring)

theorem scalarBetaSChart_hasDerivAt_x (x s : ℂ)
    (hH : betaFrameDenom x*betaFrameF x s ≠ 0) (i j : Fin 3) :
    HasDerivAt (fun z => scalarBetaSChart z s i j) (betaSourceSX x s i j) x := by
  exact (betaSourceNS_hasDerivAt x s i j).fun_div
    ((betaSourceDenom_hasDerivAt x).fun_mul (betaFrameF_hasDerivAt_x x s)) hH

theorem scalarBetaUChart_hasDerivAt_s (x s : ℂ)
    (hH : betaFrameDenom x*betaFrameF x s ≠ 0) (i j : Fin 3) :
    HasDerivAt (fun z => scalarBetaUChart x z i j) (betaSourceUS x s i j) s := by
  have hf := (((hasDerivAt_id s).fun_pow 2).fun_sub
      ((hasDerivAt_id s).const_mul (2*betaFrameMid x))).fun_add
    (hasDerivAt_const s (betaFrameLambda x))
  have hd := hf.const_mul (betaFrameDenom x)
  change HasDerivAt (fun z => betaFrameDenom x*betaFrameF x z) _ s at hd
  exact ((betaSourceNU_hasDerivAt x s i j).fun_div hd hH).congr_deriv
    (by norm_num [betaSourceUS])

theorem scalarBetaSFull_derivU (U s : ℂ) (hH : betaFrameH U s ≠ 0) :
    betaPartialU scalarBetaSFull U s=
      scalarBetaS U s-(2*U^2) • betaSourceSX (betaFrameX U) s := by
  ext i j
  change deriv (fun V => V*scalarBetaSChart (betaFrameX V) s i j) U=
    scalarBetaSChart (betaFrameX U) s i j-2*U^2*betaSourceSX (betaFrameX U) s i j
  have hc := (scalarBetaSChart_hasDerivAt_x (betaFrameX U) s hH i j).comp U
    (betaFrameX_hasDerivAt U)
  have h := (hasDerivAt_id U).fun_mul hc
  apply (h.congr_deriv ?_).deriv
  dsimp only [Function.comp_apply, id_eq]
  ring

theorem scalarBetaU_derivS (U s : ℂ) (hH : betaFrameH U s ≠ 0) :
    betaPartialS scalarBetaU U s=betaSourceUS (betaFrameX U) s := by
  ext i j
  exact (scalarBetaUChart_hasDerivAt_s (betaFrameX U) s hH i j).deriv

noncomputable def betaSourceRational (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  -scalarBetaSChart x s+(2*(1-x)) • betaSourceSX x s-
    (6*betaFrameRho*(1-x)*x^2/s) •
      (scalarBetaSChart x s*(ordinarySymmetricConnection ((betaFrameLambda x)/s)).transpose)+
    betaSourceUS x s-ordinarySymmetricConnection s*scalarBetaUChart x s+
    (betaFrameLambda x/s^2) •
      (scalarBetaUChart x s*(ordinarySymmetricConnection ((betaFrameLambda x)/s)).transpose)

theorem scalarBetaSource_rational (U s : ℂ) (hH : betaFrameH U s ≠ 0) :
    scalarBetaSource U s=betaSourceRational (betaFrameX U) s := by
  rw [scalarBetaSource, betaCovariantU, betaCovariantS,
    scalarBetaSFull_derivU U s hH, scalarBetaU_derivS U s hH]
  ext i j
  simp only [betaSourceRational, scalarBetaSFull, scalarBetaS, scalarBetaU,
    betaFrameLambdaU, betaFrameB, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_succ]
  rw [show 1-betaFrameX U=U^2 by unfold betaFrameX; ring]
  ring

theorem betaSource_discriminant (x : ℂ) :
    betaFrameMid x^2-betaFrameLambda x=(1-x)*betaFrameEll x^2*betaFrameM x := by
  norm_num only [betaFrameMid, betaFrameLambda, betaFrameEll, betaFrameM, betaFrameRho]
  ring


noncomputable def betaSourceNativeConnection (q : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0,0,6*q^2-4*q; -5/72,1-2*q,2*q*(q-1); 0,1-q,0]

theorem betaSource_connection_polynomial (q : ℂ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dualStateMatrix q*ordinarySymmetricConnection q=betaSourceNativeConnection q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [betaSourceNativeConnection, dualStateMatrix, ordinarySymmetricConnection,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [hq0, sub_ne_zero.mpr hq1.symm] <;> ring

noncomputable def betaSourceNativeRational (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  -(dualStateMatrix s*scalarBetaSChart x s*(dualStateMatrix (betaFrameLambda x/s)).transpose)+
    (2*(1-x)) •
      (dualStateMatrix s*betaSourceSX x s*(dualStateMatrix (betaFrameLambda x/s)).transpose)-
    (6*betaFrameRho*(1-x)*x^2/s) •
      (dualStateMatrix s*scalarBetaSChart x s*(betaSourceNativeConnection (betaFrameLambda x/s)).transpose)+
    dualStateMatrix s*betaSourceUS x s*(dualStateMatrix (betaFrameLambda x/s)).transpose-
    betaSourceNativeConnection s*scalarBetaUChart x s*(dualStateMatrix (betaFrameLambda x/s)).transpose+
    (betaFrameLambda x/s^2) •
      (dualStateMatrix s*scalarBetaUChart x s*(betaSourceNativeConnection (betaFrameLambda x/s)).transpose)

theorem betaSourceRational_pullback (x s : ℂ) (hx0 : x ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ betaFrameLambda x) :
    dualStateMatrix s*betaSourceRational x s*(dualStateMatrix (betaFrameLambda x/s)).transpose=
      betaSourceNativeRational x s := by
  have hl : betaFrameLambda x ≠ 0 := by simp [betaFrameLambda, betaFrameRho, hx0]
  have hb0 : betaFrameLambda x/s ≠ 0 := div_ne_zero hl hs0
  have hb1 : betaFrameLambda x/s ≠ 1 := by
    intro h
    exact hsl ((div_eq_one_iff_eq hs0).1 h).symm
  have hct : (ordinarySymmetricConnection (betaFrameLambda x/s)).transpose*
      (dualStateMatrix (betaFrameLambda x/s)).transpose=
        (betaSourceNativeConnection (betaFrameLambda x/s)).transpose := by
    rw [← Matrix.transpose_mul, betaSource_connection_polynomial _ hb0 hb1]
  have hf (B : Matrix (Fin 3) (Fin 3) ℂ) :
      dualStateMatrix s*(ordinarySymmetricConnection s*B)*
        (dualStateMatrix (betaFrameLambda x/s)).transpose=
      betaSourceNativeConnection s*B*(dualStateMatrix (betaFrameLambda x/s)).transpose := by
    rw [← Matrix.mul_assoc, betaSource_connection_polynomial s hs0 hs1]
  have hg (B : Matrix (Fin 3) (Fin 3) ℂ) :
      dualStateMatrix s*(B*(ordinarySymmetricConnection (betaFrameLambda x/s)).transpose)*
        (dualStateMatrix (betaFrameLambda x/s)).transpose=
      dualStateMatrix s*B*(betaSourceNativeConnection (betaFrameLambda x/s)).transpose := by
    simp only [Matrix.mul_assoc, hct]
  simp only [betaSourceRational, betaSourceNativeRational, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.add_mul,
    Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul, hf, hg]

set_option maxHeartbeats 2000000 in
theorem betaSourceRational_native_00 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hF : betaFrameF x s ≠ 0) (hs0 : s ≠ 0) :
    betaSourceNativeRational x s 0 0=angularLiteralSource x s 0 0 := by
  norm_num only [betaSourceNativeRational, angularLiteralSource,
    angularLiteralSource00, dualStateMatrix, betaSourceNativeConnection,
    betaSourceSX, betaSourceUS, betaSourceNS, betaSourceNSX, betaSourceNU,
    betaSourceNUS, scalarBetaSChart, scalarBetaUChart, betaFrameLP,
    betaFrameRP, betaSourceLPX, betaSourceRPX, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, zero_add, mul_zero, zero_mul]
  norm_num only [betaFrameDenom, betaSourceDX, betaFrameFX,
    betaFrameMid, betaFrameMidX, betaFrameEll, betaFrameEllX, betaFrameM,
    betaFrameLambda, betaFrameRho]
  simp only [show (25 : ℂ)-9*x= -(9*x-25) by ring]
  generalize hgF : betaFrameF x s=gF at hF ⊢
  generalize he : 99*x-50=e at hx50 ⊢
  generalize hk : 9*x-25=k at hx25 ⊢

  field_simp [hF, hx0, hx25, hx50, hs0]
  subst gF e k
  norm_num only [betaFrameF, betaFrameMid, betaFrameLambda, betaFrameRho]
  ring

set_option maxHeartbeats 2000000 in
theorem betaSourceRational_native_01 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hF : betaFrameF x s ≠ 0) (hs0 : s ≠ 0) :
    betaSourceNativeRational x s 0 1=angularLiteralSource x s 0 1 := by
  norm_num only [betaSourceNativeRational, angularLiteralSource,
    angularLiteralSource01, dualStateMatrix, betaSourceNativeConnection,
    betaSourceSX, betaSourceUS, betaSourceNS, betaSourceNSX, betaSourceNU,
    betaSourceNUS, scalarBetaSChart, scalarBetaUChart, betaFrameLP,
    betaFrameRP, betaSourceLPX, betaSourceRPX, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, zero_add, mul_zero, zero_mul]
  norm_num only [betaFrameDenom, betaSourceDX, betaFrameFX,
    betaFrameMid, betaFrameMidX, betaFrameEll, betaFrameEllX, betaFrameM,
    betaFrameLambda, betaFrameRho]
  simp only [show (25 : ℂ)-9*x= -(9*x-25) by ring]
  generalize hgF : betaFrameF x s=gF at hF ⊢
  generalize he : 99*x-50=e at hx50 ⊢
  generalize hk : 9*x-25=k at hx25 ⊢

  field_simp [hF, hx0, hx25, hx50, hs0]
  subst gF e k
  norm_num only [betaFrameF, betaFrameMid, betaFrameLambda, betaFrameRho]
  ring

set_option maxHeartbeats 2000000 in
theorem betaSourceRational_native_02 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hF : betaFrameF x s ≠ 0) (hs0 : s ≠ 0) :
    betaSourceNativeRational x s 0 2=angularLiteralSource x s 0 2 := by
  norm_num only [betaSourceNativeRational, angularLiteralSource,
    angularLiteralSource02, dualStateMatrix, betaSourceNativeConnection,
    betaSourceSX, betaSourceUS, betaSourceNS, betaSourceNSX, betaSourceNU,
    betaSourceNUS, scalarBetaSChart, scalarBetaUChart, betaFrameLP,
    betaFrameRP, betaSourceLPX, betaSourceRPX, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, zero_add, mul_zero, zero_mul]
  norm_num only [betaFrameDenom, betaSourceDX, betaFrameFX,
    betaFrameMid, betaFrameMidX, betaFrameEll, betaFrameEllX, betaFrameM,
    betaFrameLambda, betaFrameRho]
  simp only [show (25 : ℂ)-9*x= -(9*x-25) by ring]
  generalize hgF : betaFrameF x s=gF at hF ⊢
  generalize he : 99*x-50=e at hx50 ⊢
  generalize hk : 9*x-25=k at hx25 ⊢

  field_simp [hF, hx0, hx25, hx50, hs0]
  subst gF e k
  norm_num only [betaFrameF, betaFrameMid, betaFrameLambda, betaFrameRho]
  ring

set_option maxHeartbeats 2000000 in
theorem betaSourceRational_native_10 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hF : betaFrameF x s ≠ 0) (hs0 : s ≠ 0) :
    betaSourceNativeRational x s 1 0=angularLiteralSource x s 1 0 := by
  norm_num only [betaSourceNativeRational, angularLiteralSource,
    angularLiteralSource10, dualStateMatrix, betaSourceNativeConnection,
    betaSourceSX, betaSourceUS, betaSourceNS, betaSourceNSX, betaSourceNU,
    betaSourceNUS, scalarBetaSChart, scalarBetaUChart, betaFrameLP,
    betaFrameRP, betaSourceLPX, betaSourceRPX, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, zero_add, mul_zero, zero_mul]
  norm_num only [betaFrameDenom, betaSourceDX, betaFrameFX,
    betaFrameMid, betaFrameMidX, betaFrameEll, betaFrameEllX, betaFrameM,
    betaFrameLambda, betaFrameRho]
  simp only [show (25 : ℂ)-9*x= -(9*x-25) by ring]
  generalize hgF : betaFrameF x s=gF at hF ⊢
  generalize he : 99*x-50=e at hx50 ⊢
  generalize hk : 9*x-25=k at hx25 ⊢

  field_simp [hF, hx0, hx25, hx50, hs0]
  subst gF e k
  norm_num only [betaFrameF, betaFrameMid, betaFrameLambda, betaFrameRho]
  ring

set_option maxHeartbeats 2000000 in
theorem betaSourceRational_native_11 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hF : betaFrameF x s ≠ 0) (hs0 : s ≠ 0) :
    betaSourceNativeRational x s 1 1=angularLiteralSource x s 1 1 := by
  norm_num only [betaSourceNativeRational, angularLiteralSource,
    angularLiteralSource11, dualStateMatrix, betaSourceNativeConnection,
    betaSourceSX, betaSourceUS, betaSourceNS, betaSourceNSX, betaSourceNU,
    betaSourceNUS, scalarBetaSChart, scalarBetaUChart, betaFrameLP,
    betaFrameRP, betaSourceLPX, betaSourceRPX, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, zero_add, mul_zero, zero_mul]
  norm_num only [betaFrameDenom, betaSourceDX, betaFrameFX,
    betaFrameMid, betaFrameMidX, betaFrameEll, betaFrameEllX, betaFrameM,
    betaFrameLambda, betaFrameRho]
  simp only [show (25 : ℂ)-9*x= -(9*x-25) by ring]
  generalize hgF : betaFrameF x s=gF at hF ⊢
  generalize he : 99*x-50=e at hx50 ⊢
  generalize hk : 9*x-25=k at hx25 ⊢

  field_simp [hF, hx0, hx25, hx50, hs0]
  subst gF e k
  norm_num only [betaFrameF, betaFrameMid, betaFrameLambda, betaFrameRho]
  ring

set_option maxHeartbeats 2000000 in
theorem betaSourceRational_native_12 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hF : betaFrameF x s ≠ 0) (hs0 : s ≠ 0) :
    betaSourceNativeRational x s 1 2=angularLiteralSource x s 1 2 := by
  norm_num only [betaSourceNativeRational, angularLiteralSource,
    angularLiteralSource12, dualStateMatrix, betaSourceNativeConnection,
    betaSourceSX, betaSourceUS, betaSourceNS, betaSourceNSX, betaSourceNU,
    betaSourceNUS, scalarBetaSChart, scalarBetaUChart, betaFrameLP,
    betaFrameRP, betaSourceLPX, betaSourceRPX, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, zero_add, mul_zero, zero_mul]
  norm_num only [betaFrameDenom, betaSourceDX, betaFrameFX,
    betaFrameMid, betaFrameMidX, betaFrameEll, betaFrameEllX, betaFrameM,
    betaFrameLambda, betaFrameRho]
  simp only [show (25 : ℂ)-9*x= -(9*x-25) by ring]
  generalize hgF : betaFrameF x s=gF at hF ⊢
  generalize he : 99*x-50=e at hx50 ⊢
  generalize hk : 9*x-25=k at hx25 ⊢

  field_simp [hF, hx0, hx25, hx50, hs0]
  subst gF e k
  norm_num only [betaFrameF, betaFrameMid, betaFrameLambda, betaFrameRho]
  ring

set_option maxHeartbeats 2000000 in
theorem betaSourceRational_native_20 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hF : betaFrameF x s ≠ 0) (hs0 : s ≠ 0) :
    betaSourceNativeRational x s 2 0=angularLiteralSource x s 2 0 := by
  norm_num only [betaSourceNativeRational, angularLiteralSource,
    angularLiteralSource20, dualStateMatrix, betaSourceNativeConnection,
    betaSourceSX, betaSourceUS, betaSourceNS, betaSourceNSX, betaSourceNU,
    betaSourceNUS, scalarBetaSChart, scalarBetaUChart, betaFrameLP,
    betaFrameRP, betaSourceLPX, betaSourceRPX, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, zero_add, mul_zero, zero_mul]
  norm_num only [betaFrameDenom, betaSourceDX, betaFrameFX,
    betaFrameMid, betaFrameMidX, betaFrameEll, betaFrameEllX, betaFrameM,
    betaFrameLambda, betaFrameRho]
  simp only [show (25 : ℂ)-9*x= -(9*x-25) by ring]
  generalize hgF : betaFrameF x s=gF at hF ⊢
  generalize he : 99*x-50=e at hx50 ⊢
  generalize hk : 9*x-25=k at hx25 ⊢

  field_simp [hF, hx0, hx25, hx50, hs0]
  subst gF e k
  norm_num only [betaFrameF, betaFrameMid, betaFrameLambda, betaFrameRho]
  ring

set_option maxHeartbeats 2000000 in
theorem betaSourceRational_native_21 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hF : betaFrameF x s ≠ 0) (hs0 : s ≠ 0) :
    betaSourceNativeRational x s 2 1=angularLiteralSource x s 2 1 := by
  norm_num only [betaSourceNativeRational, angularLiteralSource,
    angularLiteralSource21, dualStateMatrix, betaSourceNativeConnection,
    betaSourceSX, betaSourceUS, betaSourceNS, betaSourceNSX, betaSourceNU,
    betaSourceNUS, scalarBetaSChart, scalarBetaUChart, betaFrameLP,
    betaFrameRP, betaSourceLPX, betaSourceRPX, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, zero_add, mul_zero, zero_mul]
  norm_num only [betaFrameDenom, betaSourceDX, betaFrameFX,
    betaFrameMid, betaFrameMidX, betaFrameEll, betaFrameEllX, betaFrameM,
    betaFrameLambda, betaFrameRho]
  simp only [show (25 : ℂ)-9*x= -(9*x-25) by ring]
  generalize hgF : betaFrameF x s=gF at hF ⊢
  generalize he : 99*x-50=e at hx50 ⊢
  generalize hk : 9*x-25=k at hx25 ⊢

  field_simp [hF, hx0, hx25, hx50, hs0]
  subst gF e k
  norm_num only [betaFrameF, betaFrameMid, betaFrameLambda, betaFrameRho]
  ring

set_option maxHeartbeats 2000000 in
theorem betaSourceRational_native_22 (x s : ℂ) (_hx0 : x ≠ 0)
    (_hx25 : 9*x-25 ≠ 0) (_hx50 : 99*x-50 ≠ 0)
    (_hF : betaFrameF x s ≠ 0) (_hs0 : s ≠ 0) :
    betaSourceNativeRational x s 2 2=angularLiteralSource x s 2 2 := by
  norm_num only [betaSourceNativeRational, angularLiteralSource,
    angularLiteralSource22, dualStateMatrix, betaSourceNativeConnection,
    betaSourceSX, betaSourceUS, betaSourceNS, betaSourceNSX, betaSourceNU,
    betaSourceNUS, scalarBetaSChart, scalarBetaUChart, betaFrameLP,
    betaFrameRP, betaSourceLPX, betaSourceRPX, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, zero_add, mul_zero,
    zero_mul, zero_div, zero_sub, sub_zero, neg_zero]
theorem betaSourceRational_native (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hF : betaFrameF x s ≠ 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsl : s ≠ betaFrameLambda x) :
    dualStateMatrix s*betaSourceRational x s*(dualStateMatrix ((betaFrameLambda x)/s)).transpose=
      angularLiteralSource x s := by
  rw [betaSourceRational_pullback x s hx0 hs0 hs1 hsl]
  ext i j
  fin_cases i <;> fin_cases j
  · exact betaSourceRational_native_00 x s hx0 hx25 hx50 hF hs0
  · exact betaSourceRational_native_01 x s hx0 hx25 hx50 hF hs0
  · exact betaSourceRational_native_02 x s hx0 hx25 hx50 hF hs0
  · exact betaSourceRational_native_10 x s hx0 hx25 hx50 hF hs0
  · exact betaSourceRational_native_11 x s hx0 hx25 hx50 hF hs0
  · exact betaSourceRational_native_12 x s hx0 hx25 hx50 hF hs0
  · exact betaSourceRational_native_20 x s hx0 hx25 hx50 hF hs0
  · exact betaSourceRational_native_21 x s hx0 hx25 hx50 hF hs0
  · exact betaSourceRational_native_22 x s hx0 hx25 hx50 hF hs0

theorem scalarBetaSource_native (U s : ℂ) (hH : betaFrameH U s ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ betaFrameLambda (betaFrameX U)) :
    dualStateMatrix s*scalarBetaSource U s*(dualStateMatrix (betaFrameB U s)).transpose=
      angularLiteralSource (betaFrameX U) s := by
  have hd := (mul_ne_zero_iff.1 hH).1
  have hF := (mul_ne_zero_iff.1 hH).2
  have hx0 : betaFrameX U ≠ 0 := by
    intro h
    simp [betaFrameDenom, h] at hd
  have hx25 : 9*betaFrameX U-25 ≠ 0 := by
    intro h
    have hM : betaFrameM (betaFrameX U)=0 := by
      unfold betaFrameM
      linear_combination -h
    simp [betaFrameDenom, hM] at hd
  have hx50 : 99*betaFrameX U-50 ≠ 0 := by
    intro h
    simp [betaFrameDenom, h] at hd
  rw [scalarBetaSource_rational U s hH]
  exact betaSourceRational_native (betaFrameX U) s hx0 hx25 hx50 hF hs0 hs1 hsl

theorem betaPair_dual_pullback (B : Matrix (Fin 3) (Fin 3) ℂ) (s b : ℂ) :
    betaPair B (dualState s) (dualState b)=
      angularTensorPair (dualStateMatrix s*B*(dualStateMatrix b).transpose)
        (nativeState s) (nativeState b) := by
  simp [betaPair, angularTensorPair, dualState, Matrix.mul_apply, Matrix.mulVec,
    Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  ring

theorem scalarBetaSource_actual_integrand (U s : ℂ) (hH : betaFrameH U s ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ betaFrameLambda (betaFrameX U)) :
    betaPair (scalarBetaSource U s) (dualState s) (dualState (betaFrameB U s))=
      angularSourceIntegrand (betaFrameX U) s := by
  rw [betaPair_dual_pullback, scalarBetaSource_native U s hH hs0 hs1 hsl]
  rfl

theorem angularSource_actual_beta_derivatives (U s : ℂ) (hH : betaFrameH U s ≠ 0)
    (hs : ‖s‖ < 1) (hs0 : s ≠ 0) (hsl : s ≠ betaFrameLambda (betaFrameX U))
    (hb : ‖betaFrameB U s‖ < 1) (hb0 : betaFrameB U s ≠ 0) :
    angularSourceIntegrand (betaFrameX U) s=
      -deriv (fun V => betaPair (scalarBetaSFull V s) (dualState s)
        (dualState (betaFrameB V s))) U+
      deriv (fun z => betaPair (scalarBetaU U z) (dualState z)
        (dualState (betaFrameB U z))) s := by
  have hs1 : s ≠ 1 := by
    intro h
    simp [h] at hs
  rw [← scalarBetaSource_actual_integrand U s hH hs0 hs1 hsl]
  exact scalarBetaSource_pair_identity U s hH hs hs0 hb hb0

end Row12

#print axioms Row12.betaSourceLP_deriv
#print axioms Row12.betaSourceRP_deriv
#print axioms Row12.betaSourceDenom_hasDerivAt
#print axioms Row12.betaSourceNS_hasDerivAt
#print axioms Row12.betaSourceNU_hasDerivAt
#print axioms Row12.scalarBetaSChart_hasDerivAt_x
#print axioms Row12.scalarBetaUChart_hasDerivAt_s
#print axioms Row12.scalarBetaSFull_derivU
#print axioms Row12.scalarBetaU_derivS
#print axioms Row12.scalarBetaSource_rational
#print axioms Row12.betaSource_discriminant
#print axioms Row12.betaSourceRational_native
#print axioms Row12.scalarBetaSource_native
#print axioms Row12.betaPair_dual_pullback
#print axioms Row12.scalarBetaSource_actual_integrand
#print axioms Row12.angularSource_actual_beta_derivatives

#print axioms Row12.betaSource_connection_polynomial
#print axioms Row12.betaSourceRational_pullback
#print axioms Row12.betaSourceRational_native_00
#print axioms Row12.betaSourceRational_native_01
#print axioms Row12.betaSourceRational_native_02
#print axioms Row12.betaSourceRational_native_10
#print axioms Row12.betaSourceRational_native_11
#print axioms Row12.betaSourceRational_native_12
#print axioms Row12.betaSourceRational_native_20
#print axioms Row12.betaSourceRational_native_21
#print axioms Row12.betaSourceRational_native_22
