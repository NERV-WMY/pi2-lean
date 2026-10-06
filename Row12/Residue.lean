import Row12.Convergence
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Row12

noncomputable def contactStateMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  let q : ℝ := 27 / 125
  !![-5*q/72, 0, 2*q^2*(1-q); -q/2, q*(q-1), 0; 1-q, 0, 0]

noncomputable def contactSourceMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  let j : ℝ := 40000 / 189
  let ell : ℝ := -3 / 1280
  let c : ℝ := 5 / 147456
  c • !![0, 0, j^2; 0, 2*j^2, 2*ell*j^3; j^2, 2*ell*j^3, ell^2*j^4]

noncomputable def contactResidueMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1/750, 1/150, 98/1125; 1/150, 98/1125, 0; 98/1125, 0, 0]

theorem contact_matrix_product :
    contactStateMatrix * contactSourceMatrix * contactStateMatrix.transpose =
      contactResidueMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [contactStateMatrix, contactSourceMatrix, contactResidueMatrix,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

noncomputable def residueForm (F DF D2F : ℝ) : ℝ :=
  dotProduct ![F, DF, D2F] (Matrix.mulVec contactResidueMatrix ![F, DF, D2F])

theorem residueForm_eq (F DF D2F : ℝ) :
    residueForm F DF D2F = -F^2/750 + F*DF/75 +
      196*F*D2F/1125 + 98*DF^2/1125 := by
  simp [residueForm, contactResidueMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

theorem residue_perfectSquare (g dg : ℝ) :
    residueForm (g^2) (2*g*dg)
      (2*dg^2+2*g*((27/196)*dg+(15/1568)*g)) =
      (3*g^2+56*g*dg)^2/4500 := by
  rw [residueForm_eq]
  ring

theorem wronskian_contact_square (g dg Z dZ : ℝ)
    (hZ : Z = Real.sqrt 2 * g)
    (hdZ : dZ = -Real.sqrt 2 * dg - (3*Real.sqrt 2/28)*g)
    (hW : g*dZ-Z*dg = -1/(2*Real.pi*Real.sqrt (1-27/125))) :
    (3*g^2+56*g*dg)^2 = 125/Real.pi^2 := by
  have hleft : (g*dZ-Z*dg)^2 = (3*g^2+56*g*dg)^2/392 := by
    rw [hZ, hdZ]
    calc
      (g*(-Real.sqrt 2*dg-(3*Real.sqrt 2/28)*g)-Real.sqrt 2*g*dg)^2 =
          (Real.sqrt 2)^2*(3*g^2+56*g*dg)^2/784 := by ring
      _ = (3*g^2+56*g*dg)^2/392 := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring
  have hright : (-1/(2*Real.pi*Real.sqrt (1-27/125)))^2 =
      125/(392*Real.pi^2) := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1-27/125)]
    field_simp [Real.pi_ne_zero]
    ring
  calc
    (3*g^2+56*g*dg)^2 = 392*(g*dZ-Z*dg)^2 := by rw [hleft]; ring
    _ = 125/Real.pi^2 := by rw [hW, hright]; ring

theorem residue_at_wronskian (g dg Z dZ : ℝ)
    (hZ : Z = Real.sqrt 2 * g)
    (hdZ : dZ = -Real.sqrt 2 * dg - (3*Real.sqrt 2/28)*g)
    (hW : g*dZ-Z*dg = -1/(2*Real.pi*Real.sqrt (1-27/125))) :
    residueForm (g^2) (2*g*dg)
      (2*dg^2+2*g*((27/196)*dg+(15/1568)*g)) = 1/(36*Real.pi^2) := by
  rw [residue_perfectSquare, wronskian_contact_square g dg Z dZ hZ hdZ hW]
  ring

end Row12

#print axioms Row12.contact_matrix_product
#print axioms Row12.residueForm_eq
#print axioms Row12.residue_perfectSquare
#print axioms Row12.wronskian_contact_square
#print axioms Row12.residue_at_wronskian
