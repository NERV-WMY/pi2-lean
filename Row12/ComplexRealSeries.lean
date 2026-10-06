import Row12.ActualResidue
import Row12.BetaFrame

namespace Row12

theorem nativeEuler_ofReal (k : ℕ) (q : ℝ) :
    nativeEuler k (q:ℂ) = ((nativeEuler k q:ℝ):ℂ) := by
  unfold nativeEuler
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  push_cast
  simp only [RCLike.ofReal_real_eq_id, id_eq, RCLike.ofReal_eq_complex_ofReal]

theorem nativeState_ofReal (q : ℝ) (i : Fin 3) :
    nativeState (q:ℂ) i = ((nativeState q i:ℝ):ℂ) := by
  fin_cases i <;> simp [nativeState,nativeF,nativeEuler_ofReal]

theorem dualState_ofReal (q : ℝ) (i : Fin 3) :
    dualState (q:ℂ) i = ((dualState q i:ℝ):ℂ) := by
  rw [dual_state_formula,dual_state_formula]
  fin_cases i <;> simp [nativeF,nativeEuler_ofReal]

theorem complex_contact_pair (F DF D2F : ℂ) :
    betaPair (contactSourceMatrix.map Complex.ofReal)
      ((contactStateMatrix.map Complex.ofReal).transpose.mulVec ![F,DF,D2F])
      ((contactStateMatrix.map Complex.ofReal).transpose.mulVec ![F,DF,D2F]) =
      -F^2/750+F*DF/75+196*F*D2F/1125+98*DF^2/1125 := by
  norm_num [betaPair,contactSourceMatrix,contactStateMatrix,Matrix.mulVec,
    Matrix.transpose_apply,Matrix.map_apply,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_dual_contact_residue :
    betaPair (contactSourceMatrix.map Complex.ofReal)
      (dualState (27/125:ℂ)) (dualState (27/125:ℂ)) =
      (1/(36*Real.pi^2):ℝ) := by
  have ht : dualStateMatrix (27/125:ℂ) = contactStateMatrix.map Complex.ofReal := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [dualStateMatrix,contactStateMatrix,Matrix.map_apply]
  have hn : nativeState (27/125:ℂ) =
      ![((nativeF (27/125):ℝ):ℂ),((nativeEuler 1 (27/125):ℝ):ℂ),
        ((nativeEuler 2 (27/125):ℝ):ℂ)] := by
    ext i
    have hh := nativeState_ofReal (27/125) i
    fin_cases i <;> simpa [nativeState] using hh
  simp only [dualState,ht,hn]
  rw [complex_contact_pair]
  have he := congrArg Complex.ofReal actual_native_contact_residue
  rw [residueForm_eq] at he
  push_cast at he
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,
    Complex.ofReal_pow] at *
  exact he

end Row12

#print axioms Row12.nativeEuler_ofReal
#print axioms Row12.nativeState_ofReal
#print axioms Row12.dualState_ofReal
#print axioms Row12.complex_contact_pair
#print axioms Row12.actual_dual_contact_residue
