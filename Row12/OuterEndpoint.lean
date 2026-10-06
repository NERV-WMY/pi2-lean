import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Row12

abbrev OuterEndpointVector := Fin 6 → ℚ

/-- Literal frozen s10 cyclic_matrix; provenance is in OUTER_ENDPOINT_UNIT.md. -/
def outerCyclicMatrix : Matrix (Fin 6) (Fin 6) ℚ :=
  !![49456/125, 153648/125, 113472/125, 72/5, -3312/25, 113472/125;
      -1576/25, -4608/25, -3312/25, 0, 72/5, -3312/25;
      46/5, 108/5, 72/5, 0, 0, 72/5;
      -1, 0, 0, 0, 0, 0;
      0, -1, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0]

def outerEndpointV0 : OuterEndpointVector := ![0, 0, 0, 5/72, 0, 0]

def outerEndpointV1 : OuterEndpointVector := ![-1, -1, -1, 77/24, 77/24, 77/24]

/-- Literal frozen s14 primitive_coefficients[3]. -/
def outerXiNegFour : OuterEndpointVector :=
  ![0, 0, -4232000000/4135131, 0, 0, 0]

/-- Literal frozen s14 primitive_coefficients[2]. -/
def outerXiNegThree : OuterEndpointVector :=
  ![0, 0, 338560000/196911, 0, 0, 0]

/-- Literal frozen s14 primitive_coefficients[1]. -/
def outerXiNegTwo : OuterEndpointVector :=
  ![0, 0, -472485400/459459, 0, 0, 0]

/-- Literal frozen s14 primitive_coefficients[0]. -/
def outerXiNegOne : OuterEndpointVector :=
  ![105800/459459, 867560/459459, 103229200/459459, -169280/51051, -1388096/51051, -2268352/51051]

/-- Literal frozen s14 primitive_coefficients[4]. -/
def outerEscapeOne : OuterEndpointVector :=
  ![-78890805485931260/886402053948411, -1227125311357021190/886402053948411, -70427029255928891500/6204814377638877, -607873567055897705440/74327471429736107583, -298973396640778498112/8258607936637345287, -145365088004028281168/635277533587488099]

/-- Literal frozen s14 primitive_coefficients[5]. -/
def outerEscapeTwo : OuterEndpointVector :=
  ![-231954922267076000/229807939912551, -331597299956488000/76602646637517, -108998157631733600/5892511279809, -39913346954892419000/917623104070816143, 28252939480465998800/101958122674535127, -14427468858797595200/5997536627913831]

/-- Literal frozen s14 primitive_coefficients[6]. -/
def outerPolynomialZero : OuterEndpointVector :=
  ![-44128649359258592/31024071888194385, 623049674458568524/31024071888194385, 6660655461825680912/31024071888194385, 57598947351747925330/10618210204248015369, 370356988491186478316/8258607936637345287, 422172179336846381488/5899005669026675205]

/-- The zero-degree Laurent row retains both escape contributions. -/
def outerXiZero : OuterEndpointVector := fun i =>
  outerPolynomialZero i - outerEscapeOne i / 50 + outerEscapeTwo i / 2500

theorem outer_cyclic_mulVec_formula (v : OuterEndpointVector) :
    outerCyclicMatrix.mulVec v =
      ![(49456/125) * v 0 + (153648/125) * v 1 + (113472/125) * v 2 +
          (72/5) * v 3 - (3312/25) * v 4 + (113472/125) * v 5,
        -(1576/25) * v 0 - (4608/25) * v 1 - (3312/25) * v 2 +
          (72/5) * v 4 - (3312/25) * v 5,
        (46/5) * v 0 + (108/5) * v 1 + (72/5) * v 2 + (72/5) * v 5,
        -(v 0), -(v 1), -(v 2)] := by
  ext i
  fin_cases i <;>
    simp [outerCyclicMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem outer_cyclic_v0 :
    outerCyclicMatrix.mulVec outerEndpointV0 = ![1, 0, 0, 0, 0, 0] := by
  ext i
  fin_cases i <;>
    norm_num [outerCyclicMatrix, outerEndpointV0, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem outer_cyclic_v1 :
    outerCyclicMatrix.mulVec outerEndpointV1 = ![1, 1, 1, 1, 1, 1] := by
  ext i
  fin_cases i <;>
    norm_num [outerCyclicMatrix, outerEndpointV1, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem outer_cyclic_mulVec_injective :
    Function.Injective outerCyclicMatrix.mulVec := by
  intro v w h
  have h0 : v 0 = w 0 := by
    have hh : -(v 0) = -(w 0) := by
      simpa [outer_cyclic_mulVec_formula] using congrFun h (3 : Fin 6)
    linarith
  have h1 : v 1 = w 1 := by
    have hh : -(v 1) = -(w 1) := by
      simpa [outer_cyclic_mulVec_formula] using congrFun h (4 : Fin 6)
    linarith
  have h2 : v 2 = w 2 := by
    have hh : -(v 2) = -(w 2) := by
      simpa [outer_cyclic_mulVec_formula] using congrFun h (5 : Fin 6)
    linarith
  have h5 : v 5 = w 5 := by
    have hh := congrFun h (2 : Fin 6)
    simp [outer_cyclic_mulVec_formula] at hh
    linarith [h0, h1, h2]
  have h4 : v 4 = w 4 := by
    have hh := congrFun h (1 : Fin 6)
    simp [outer_cyclic_mulVec_formula] at hh
    linarith [h0, h1, h2, h5]
  have h3 : v 3 = w 3 := by
    have hh := congrFun h (0 : Fin 6)
    simp [outer_cyclic_mulVec_formula] at hh
    linarith [h0, h1, h2, h4, h5]
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem outer_cyclic_v0_unique (v : OuterEndpointVector)
    (h : outerCyclicMatrix.mulVec v = ![1, 0, 0, 0, 0, 0]) :
    v = outerEndpointV0 :=
  outer_cyclic_mulVec_injective (h.trans outer_cyclic_v0.symm)

theorem outer_cyclic_v1_unique (v : OuterEndpointVector)
    (h : outerCyclicMatrix.mulVec v = ![1, 1, 1, 1, 1, 1]) :
    v = outerEndpointV1 :=
  outer_cyclic_mulVec_injective (h.trans outer_cyclic_v1.symm)

theorem outer_first_coefficient :
    ((5/72 : ℚ)^2) * (729/15625) = 9/40000 := by norm_num

theorem outer_xi_neg_four_v0 :
    dotProduct outerXiNegFour outerEndpointV0 = 0 := by
  norm_num [outerXiNegFour, outerEndpointV0, dotProduct, Fin.sum_univ_succ]

theorem outer_xi_neg_three_v0 :
    dotProduct outerXiNegThree outerEndpointV0 = 0 := by
  norm_num [outerXiNegThree, outerEndpointV0, dotProduct, Fin.sum_univ_succ]

theorem outer_xi_neg_two_v0 :
    dotProduct outerXiNegTwo outerEndpointV0 = 0 := by
  norm_num [outerXiNegTwo, outerEndpointV0, dotProduct, Fin.sum_univ_succ]

theorem outer_xi_neg_one_v0 :
    dotProduct outerXiNegOne outerEndpointV0 = -105800/459459 := by
  norm_num [outerXiNegOne, outerEndpointV0, dotProduct, Fin.sum_univ_succ]

theorem outer_xi_neg_four_v1 :
    (9/40000 : ℚ) * dotProduct outerXiNegFour outerEndpointV1 = 105800/459459 := by
  norm_num [outerXiNegFour, outerEndpointV1, dotProduct, Fin.sum_univ_succ]

theorem outer_xi_zero_v0 :
    dotProduct outerXiZero outerEndpointV0 = 8464/21879 := by
  norm_num [outerXiZero, outerPolynomialZero, outerEscapeOne, outerEscapeTwo, outerEndpointV0, dotProduct, Fin.sum_univ_succ]

theorem outer_xi_neg_three_v1 :
    (9/40000 : ℚ) * dotProduct outerXiNegThree outerEndpointV1 = -8464/21879 := by
  norm_num [outerXiNegThree, outerEndpointV1, dotProduct, Fin.sum_univ_succ]

theorem outer_pole_one_cancellation :
    dotProduct outerXiNegOne outerEndpointV0 +
      (9/40000 : ℚ) * dotProduct outerXiNegFour outerEndpointV1 = 0 := by
  rw [outer_xi_neg_one_v0, outer_xi_neg_four_v1]
  norm_num

theorem outer_zero_cancellation :
    dotProduct outerXiZero outerEndpointV0 +
      (9/40000 : ℚ) * dotProduct outerXiNegThree outerEndpointV1 = 0 := by
  rw [outer_xi_zero_v0, outer_xi_neg_three_v1]
  norm_num

end Row12

#print axioms Row12.outer_cyclic_mulVec_formula
#print axioms Row12.outer_cyclic_v0
#print axioms Row12.outer_cyclic_v1
#print axioms Row12.outer_cyclic_mulVec_injective
#print axioms Row12.outer_cyclic_v0_unique
#print axioms Row12.outer_cyclic_v1_unique
#print axioms Row12.outer_first_coefficient
#print axioms Row12.outer_xi_neg_four_v0
#print axioms Row12.outer_xi_neg_three_v0
#print axioms Row12.outer_xi_neg_two_v0
#print axioms Row12.outer_xi_neg_one_v0
#print axioms Row12.outer_xi_neg_four_v1
#print axioms Row12.outer_xi_zero_v0
#print axioms Row12.outer_xi_neg_three_v1
#print axioms Row12.outer_pole_one_cancellation
#print axioms Row12.outer_zero_cancellation
