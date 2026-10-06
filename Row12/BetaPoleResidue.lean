import Row12.BetaFrame

namespace Row12

theorem scalar_beta_pole_factor {U : ℝ} (hU : 0 < U) (hU1 : U < 1) (s : ℂ) :
    betaFrameF (betaFrameX (U:ℂ)) s =
      (s-(scalarPolePlus U:ℂ))*(s-(scalarPoleMinus U:ℂ)) := by
  have hx : betaFrameX (U:ℂ) = (scalarPathX U:ℂ) := by
    simp [betaFrameX,scalarPathX]
  have hh := betaFrame_real_agreement (scalarPathX U)
  have hp : (scalarPolePlus U:ℂ)*(scalarPoleMinus U:ℂ) =
      (scalarLambda (scalarPathX U):ℂ) := by
    exact_mod_cast scalar_poles_product hU hU1
  have hs : (scalarPolePlus U:ℂ)+(scalarPoleMinus U:ℂ) =
      2*(scalarMid (scalarPathX U):ℂ) := by
    simp only [scalarPolePlus,scalarPoleMinus]
    push_cast
    ring
  simp only [betaFrameF,hx,hh.2.2.2.1,hh.2.2.2.2.2.2] 
  linear_combination s*hs-hp

theorem twoPole_partialFraction (U A B ell M d s m t : ℂ)
    (ht : t^2=M) (hd : d ≠ 0)
    (ha : s-(m+U*ell*t) ≠ 0) (hb : s-(m-U*ell*t) ≠ 0) :
    U*(2*A*(s-m)+2*ell*M*B)/(d*((s-(m+U*ell*t))*(s-(m-U*ell*t)))) =
      ((U*A+t*B)/d)/(s-(m+U*ell*t))+
      ((U*A-t*B)/d)/(s-(m-U*ell*t)) := by
  field_simp [hd,ha,hb]
  linear_combination -2*U*ell*B*ht

noncomputable def scalarBetaPositiveResidue (U : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let x : ℂ := scalarPathX U
  fun i j => ((U:ℂ)*betaFrameLP x i j+
    (Real.sqrt (scalarM (scalarPathX U)):ℂ)*betaFrameRP x i j)/betaFrameDenom x

noncomputable def scalarBetaNegativeResidue (U : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let x : ℂ := scalarPathX U
  fun i j => ((U:ℂ)*betaFrameLP x i j-
    (Real.sqrt (scalarM (scalarPathX U)):ℂ)*betaFrameRP x i j)/betaFrameDenom x

theorem scalar_beta_contact_residue :
    scalarBetaPositiveResidue 0 = contactSourceMatrix.map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  norm_num [scalarBetaPositiveResidue,scalarPathX,scalarM,betaFrameLP,betaFrameRP,
    betaFrameDenom,betaFrameM,contactSourceMatrix,Matrix.map_apply]

theorem scalar_beta_partialFractions {U : ℝ} (hU : 0 < U) (hU1 : U < 1) (s : ℂ)
    (hd : betaFrameDenom (scalarPathX U:ℂ) ≠ 0)
    (hsa : s-(scalarPolePlus U:ℂ) ≠ 0) (hsb : s-(scalarPoleMinus U:ℂ) ≠ 0) :
    scalarBetaSFull (U:ℂ) s =
      (s-(scalarPolePlus U:ℂ))⁻¹ • scalarBetaPositiveResidue U+
      (s-(scalarPoleMinus U:ℂ))⁻¹ • scalarBetaNegativeResidue U := by
  have hx : betaFrameX (U:ℂ) = (scalarPathX U:ℂ) := by
    simp [betaFrameX,scalarPathX]
  have hh := betaFrame_real_agreement (scalarPathX U)
  have ht : (Real.sqrt (scalarM (scalarPathX U)):ℂ)^2 =
      betaFrameM (scalarPathX U:ℂ) := by
    rw [hh.2.2.1]
    exact_mod_cast Real.sq_sqrt (scalarM_pos (scalarPathX_mem hU hU1).2).le
  have hplus : (scalarPolePlus U:ℂ) = betaFrameMid (scalarPathX U:ℂ)+
      (U:ℂ)*betaFrameEll (scalarPathX U:ℂ)*(Real.sqrt (scalarM (scalarPathX U)):ℂ) := by
    rw [hh.2.2.2.1,hh.2.2.2.2.1]
    simp [scalarPolePlus]
  have hminus : (scalarPoleMinus U:ℂ) = betaFrameMid (scalarPathX U:ℂ)-
      (U:ℂ)*betaFrameEll (scalarPathX U:ℂ)*(Real.sqrt (scalarM (scalarPathX U)):ℂ) := by
    rw [hh.2.2.2.1,hh.2.2.2.2.1]
    simp [scalarPoleMinus]
  ext i j
  have he := twoPole_partialFraction (U:ℂ)
    (betaFrameLP (scalarPathX U:ℂ) i j) (betaFrameRP (scalarPathX U:ℂ) i j)
    (betaFrameEll (scalarPathX U:ℂ)) (betaFrameM (scalarPathX U:ℂ))
    (betaFrameDenom (scalarPathX U:ℂ)) s (betaFrameMid (scalarPathX U:ℂ))
    (Real.sqrt (scalarM (scalarPathX U)):ℂ) ht hd
    (hplus ▸ hsa) (hminus ▸ hsb)
  rw [← hplus,← hminus,mul_div_assoc] at he
  have hf : betaFrameF (scalarPathX U:ℂ) s =
      (s-(scalarPolePlus U:ℂ))*(s-(scalarPoleMinus U:ℂ)) := by
    rw [← hx]
    exact scalar_beta_pole_factor hU hU1 s
  change (U:ℂ)*((2*betaFrameLP (betaFrameX (U:ℂ)) i j*(s-betaFrameMid (betaFrameX (U:ℂ)))+
    2*betaFrameEll (betaFrameX (U:ℂ))*betaFrameM (betaFrameX (U:ℂ))*
      betaFrameRP (betaFrameX (U:ℂ)) i j)/
      (betaFrameDenom (betaFrameX (U:ℂ))*betaFrameF (betaFrameX (U:ℂ)) s)) =
    (s-(scalarPolePlus U:ℂ))⁻¹*
      (((U:ℂ)*betaFrameLP (scalarPathX U:ℂ) i j+
        (Real.sqrt (scalarM (scalarPathX U)):ℂ)*betaFrameRP (scalarPathX U:ℂ) i j)/
        betaFrameDenom (scalarPathX U:ℂ))+
    (s-(scalarPoleMinus U:ℂ))⁻¹*
      (((U:ℂ)*betaFrameLP (scalarPathX U:ℂ) i j-
        (Real.sqrt (scalarM (scalarPathX U)):ℂ)*betaFrameRP (scalarPathX U:ℂ) i j)/
        betaFrameDenom (scalarPathX U:ℂ))
  rw [hx,hf]
  simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using he

end Row12

#print axioms Row12.scalar_beta_pole_factor
#print axioms Row12.twoPole_partialFraction
#print axioms Row12.scalar_beta_contact_residue
#print axioms Row12.scalar_beta_partialFractions
