import Row12.DualFrame
import Row12.SixthSeries

namespace Row12

noncomputable def angularNFWeight : Fin 3 → ℂ := ![5/72, 23/36, 3/2]

noncomputable def angularNFFirst (v : Fin 6 → ℂ) : Fin 3 → ℂ := ![v 0, v 1, v 2]

noncomputable def angularNFSecond (v : Fin 6 → ℂ) : Fin 3 → ℂ := ![v 3, v 4, v 5]

noncomputable def angularNFRow (v : Fin 6 → ℂ) (lambda s : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  angularNFWeight i * angularNFFirst v j / (s-1) +
    angularNFSecond v i * angularNFWeight j / (s-lambda)

noncomputable def angularNFParameterDerivative (v : Fin 6 → ℂ) (lambda s : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  angularNFSecond v i * angularNFWeight j / (s-lambda)^2

noncomputable def angularNFPrimitiveRow (v : Fin 6 → ℂ) (lambda s : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  -s * (angularNFSecond v i * angularNFWeight j) / (s-lambda)

noncomputable def angularNFPrimitiveDerivative (v : Fin 6 → ℂ) (lambda s : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ := lambda • angularNFParameterDerivative v lambda s

noncomputable def angularRowSAction (R : Matrix (Fin 3) (Fin 3) ℂ) (lambda s : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  s⁻¹ • ((nativeEulerConnection s).transpose * R - R * nativeEulerConnection (lambda/s))

noncomputable def angularAnchorRow : Matrix (Fin 3) (Fin 3) ℂ :=
  !![46/5, 108/5, 72/5; -1576/25, -4608/25, -3312/25;
    49456/125, 153648/125, 113472/125]

noncomputable def angularHolomorphicRow (s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![s⁻¹, 0, 0; 0, 0, 0; 0, 0, 0]

theorem angular_nf_parameter_entry_hasDerivAt (v : Fin 6 → ℂ) (lambda s : ℂ)
    (hsl : s ≠ lambda) (i j : Fin 3) :
    HasDerivAt (fun z => angularNFRow v z s i j)
      (angularNFParameterDerivative v lambda s i j) lambda := by
  have hden : s-lambda ≠ 0 := sub_ne_zero.mpr hsl
  have h := (hasDerivAt_const lambda (angularNFWeight i * angularNFFirst v j / (s-1))).add
    ((hasDerivAt_const lambda (angularNFSecond v i * angularNFWeight j)).div
      ((hasDerivAt_const lambda s).fun_sub (hasDerivAt_id lambda)) hden)
  exact h.congr_deriv (by simp [angularNFParameterDerivative])

theorem angular_nf_primitive_entry_hasDerivAt (v : Fin 6 → ℂ) (lambda s : ℂ)
    (hsl : s ≠ lambda) (i j : Fin 3) :
    HasDerivAt (fun z => angularNFPrimitiveRow v lambda z i j)
      (angularNFPrimitiveDerivative v lambda s i j) s := by
  have hden : s-lambda ≠ 0 := sub_ne_zero.mpr hsl
  let c := angularNFSecond v i * angularNFWeight j
  have h := ((hasDerivAt_id s).const_mul (-c)).div
    ((hasDerivAt_id s).fun_sub (hasDerivAt_const s lambda)) hden
  have hf : (fun z : ℂ => (-c)*z/(z-lambda)) =
      (fun z => angularNFPrimitiveRow v lambda z i j) := by
    funext z
    dsimp [angularNFPrimitiveRow, c]
    ring
  change HasDerivAt (fun z : ℂ => (-c)*z/(z-lambda)) _ s at h
  rw [hf] at h
  exact h.congr_deriv (by simp [angularNFPrimitiveDerivative,
    angularNFParameterDerivative, smul_eq_mul, c]; ring)

theorem angular_nf_anchor (lambda s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsl : s ≠ lambda) :
    angularHolomorphicRow s = angularNFRow (sixthCyclicMatrix 0) lambda s +
      angularRowSAction angularAnchorRow lambda s := by
  have hb1 : lambda/s ≠ 1 := by
    intro h
    have he := (div_eq_one_iff_eq hs0).1 h
    exact hsl he.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [angularHolomorphicRow, angularNFRow, angularNFFirst, angularNFSecond,
      angularNFWeight, sixthCyclicMatrix, outerCyclicMatrix, angularRowSAction,
      angularAnchorRow, nativeEulerConnection, Matrix.mul_apply, Matrix.transpose_apply,
      smul_eq_mul, Fin.sum_univ_succ] <;>
    field_simp [hs0, sub_ne_zero.mpr hs1, sub_ne_zero.mpr hsl,
      sub_ne_zero.mpr (Ne.symm hs1), sub_ne_zero.mpr (Ne.symm hb1)] <;> ring

theorem angular_nf_euler_action (v : Fin 6 → ℂ) (lambda s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ lambda) (hl1 : lambda ≠ 1) :
    lambda • angularNFParameterDerivative v lambda s +
        angularNFRow v lambda s * nativeEulerConnection (lambda/s) =
      angularNFRow (Matrix.vecMul v (sixthB6 lambda)) lambda s +
        angularNFPrimitiveDerivative v lambda s +
        angularRowSAction (angularNFPrimitiveRow v lambda s) lambda s := by
  have hb1 : lambda/s ≠ 1 := by
    intro h
    exact hsl ((div_eq_one_iff_eq hs0).1 h).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [angularNFRow, angularNFParameterDerivative, angularNFPrimitiveDerivative,
      angularNFPrimitiveRow, angularNFFirst, angularNFSecond, angularNFWeight,
      angularRowSAction, nativeEulerConnection, sixthB6, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.vecHead, Matrix.vecTail, smul_eq_mul,
      Fin.sum_univ_succ] <;>
    field_simp [hs0, sub_ne_zero.mpr hs1, sub_ne_zero.mpr hsl,
      sub_ne_zero.mpr (Ne.symm hs1), sub_ne_zero.mpr (Ne.symm hb1),
      sub_ne_zero.mpr (Ne.symm hl1)] <;> ring

noncomputable def angularTensorPair (R : Matrix (Fin 3) (Fin 3) ℂ)
    (X Z : Fin 3 → ℂ) : ℂ := ∑ i : Fin 3, ∑ j : Fin 3, R i j * X i * Z j

theorem angular_tensor_pair_add (R S : Matrix (Fin 3) (Fin 3) ℂ) (X Z : Fin 3 → ℂ) :
    angularTensorPair (R+S) X Z = angularTensorPair R X Z + angularTensorPair S X Z := by
  simp [angularTensorPair, add_mul, Finset.sum_add_distrib]

theorem angular_tensor_pair_smul (c : ℂ) (R : Matrix (Fin 3) (Fin 3) ℂ)
    (X Z : Fin 3 → ℂ) :
    angularTensorPair (c • R) X Z = c * angularTensorPair R X Z := by
  simp [angularTensorPair, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem angular_tensor_pair_left (A R : Matrix (Fin 3) (Fin 3) ℂ) (X Z : Fin 3 → ℂ) :
    angularTensorPair (A.transpose*R) X Z = angularTensorPair R (A.mulVec X) Z := by
  simp [angularTensorPair, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem angular_tensor_pair_right (A R : Matrix (Fin 3) (Fin 3) ℂ) (X Z : Fin 3 → ℂ) :
    angularTensorPair (R*A) X Z = angularTensorPair R X (A.mulVec Z) := by
  simp [angularTensorPair, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem angular_tensor_pair_hasDerivAt
    (R : ℂ → Matrix (Fin 3) (Fin 3) ℂ) (R' : Matrix (Fin 3) (Fin 3) ℂ)
    (X Z : ℂ → Fin 3 → ℂ) (X' Z' : Fin 3 → ℂ) (q : ℂ)
    (hR : ∀ i j, HasDerivAt (fun z => R z i j) (R' i j) q)
    (hX : HasDerivAt X X' q) (hZ : HasDerivAt Z Z' q) :
    HasDerivAt (fun z => angularTensorPair (R z) (X z) (Z z))
      (angularTensorPair R' (X q) (Z q) + angularTensorPair (R q) X' (Z q) +
        angularTensorPair (R q) (X q) Z') q := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      ((hR i j).mul (hasDerivAt_pi.1 hX i)).mul (hasDerivAt_pi.1 hZ j)))
  have hf : (∑ i : Fin 3, ∑ j : Fin 3,
      (fun z => R z i j) * (fun z => X z i) * (fun z => Z z j)) =
      (fun z => angularTensorPair (R z) (X z) (Z z)) := by
    funext z
    simp [angularTensorPair, Finset.sum_apply, Pi.mul_apply]
  rw [hf] at h
  exact h.congr_deriv (by simp [angularTensorPair, Fin.sum_univ_succ]; ring)

noncomputable def angularNFIntegrand (v : Fin 6 → ℂ) (lambda s : ℂ) : ℂ :=
  angularTensorPair (angularNFRow v lambda s) (nativeState s) (nativeState (lambda/s))

noncomputable def angularNFPrimitive (v : Fin 6 → ℂ) (lambda s : ℂ) : ℂ :=
  angularTensorPair (angularNFPrimitiveRow v lambda s) (nativeState s) (nativeState (lambda/s))

noncomputable def angularSixIntegrands (lambda s : ℂ) : Fin 6 → ℂ := fun k =>
  angularNFIntegrand (Pi.single k 1) lambda s

noncomputable def angularAnchorPrimitive (lambda s : ℂ) : ℂ :=
  angularTensorPair angularAnchorRow (nativeState s) (nativeState (lambda/s))

theorem angular_nf_integrand_formula (v : Fin 6 → ℂ) (lambda s : ℂ) :
    angularNFIntegrand v lambda s =
      dotProduct angularNFWeight (nativeState s) *
          dotProduct (angularNFFirst v) (nativeState (lambda/s)) / (s-1) +
        dotProduct (angularNFSecond v) (nativeState s) *
          dotProduct angularNFWeight (nativeState (lambda/s)) / (s-lambda) := by
  simp [angularNFIntegrand, angularTensorPair, angularNFRow, dotProduct,
    Fin.sum_univ_succ, div_eq_mul_inv]
  ring

theorem angular_native_second_s_hasDerivAt (lambda s : ℂ) (hl0 : lambda ≠ 0)
    (hs0 : s ≠ 0) (hb : ‖lambda/s‖ < 1) :
    HasDerivAt (fun z : ℂ => nativeState (lambda/z))
      ((-s⁻¹) • (nativeEulerConnection (lambda/s)).mulVec (nativeState (lambda/s))) s := by
  have hb0 : lambda/s ≠ 0 := div_ne_zero hl0 hs0
  have hb1 : lambda/s ≠ 1 := by intro h; simp [h] at hb
  have hq := (hasDerivAt_const s lambda).div (hasDerivAt_id s) hs0
  have h := (native_state_hasDerivAt (lambda/s) hb hb0).scomp s hq
  apply h.congr_deriv
  rw [native_state_derivative_connection (lambda/s) hb0 hb1]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, id_eq]
  field_simp [hl0, hs0]
  ring

theorem angular_native_second_parameter_hasDerivAt (lambda s : ℂ) (hl0 : lambda ≠ 0)
    (hs0 : s ≠ 0) (hb : ‖lambda/s‖ < 1) :
    HasDerivAt (fun z : ℂ => nativeState (z/s))
      (lambda⁻¹ • (nativeEulerConnection (lambda/s)).mulVec (nativeState (lambda/s))) lambda := by
  have hb0 : lambda/s ≠ 0 := div_ne_zero hl0 hs0
  have hb1 : lambda/s ≠ 1 := by intro h; simp [h] at hb
  have hq := (hasDerivAt_id lambda).div_const s
  have h := (native_state_hasDerivAt (lambda/s) hb hb0).scomp lambda hq
  apply h.congr_deriv
  rw [native_state_derivative_connection (lambda/s) hb0 hb1]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hl0, hs0]

theorem angular_tensor_pair_s_action (R : Matrix (Fin 3) (Fin 3) ℂ)
    (X Z : Fin 3 → ℂ) (lambda s : ℂ) :
    angularTensorPair (angularRowSAction R lambda s) X Z =
      angularTensorPair R (s⁻¹ • (nativeEulerConnection s).mulVec X) Z +
        angularTensorPair R X ((-s⁻¹) • (nativeEulerConnection (lambda/s)).mulVec Z) := by
  simp [angularRowSAction, angularTensorPair, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, smul_eq_mul, Fin.sum_univ_succ]
  ring

theorem angular_native_pair_s_hasDerivAt
    (R : ℂ → Matrix (Fin 3) (Fin 3) ℂ) (R' : Matrix (Fin 3) (Fin 3) ℂ)
    (lambda s : ℂ) (hl0 : lambda ≠ 0) (hs0 : s ≠ 0)
    (hs : ‖s‖ < 1) (hb : ‖lambda/s‖ < 1)
    (hR : ∀ i j, HasDerivAt (fun z => R z i j) (R' i j) s) :
    HasDerivAt (fun z => angularTensorPair (R z) (nativeState z) (nativeState (lambda/z)))
      (angularTensorPair R' (nativeState s) (nativeState (lambda/s)) +
        angularTensorPair (angularRowSAction (R s) lambda s)
          (nativeState s) (nativeState (lambda/s))) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hX := (native_state_hasDerivAt s hs hs0).congr_deriv
    (native_state_derivative_connection s hs0 hs1)
  have hZ := angular_native_second_s_hasDerivAt lambda s hl0 hs0 hb
  have h := angular_tensor_pair_hasDerivAt R R' nativeState
    (fun z => nativeState (lambda/z)) _ _ s hR hX hZ
  exact h.congr_deriv (by rw [angular_tensor_pair_s_action]; ring)

theorem angular_nf_primitive_hasDerivAt (v : Fin 6 → ℂ) (lambda s : ℂ)
    (hl0 : lambda ≠ 0) (hs0 : s ≠ 0) (hsl : s ≠ lambda)
    (hs : ‖s‖ < 1) (hb : ‖lambda/s‖ < 1) :
    HasDerivAt (angularNFPrimitive v lambda)
      (angularTensorPair (angularNFPrimitiveDerivative v lambda s)
          (nativeState s) (nativeState (lambda/s)) +
        angularTensorPair (angularRowSAction (angularNFPrimitiveRow v lambda s) lambda s)
          (nativeState s) (nativeState (lambda/s))) s :=
  angular_native_pair_s_hasDerivAt (angularNFPrimitiveRow v lambda)
    (angularNFPrimitiveDerivative v lambda s) lambda s hl0 hs0 hs hb
    (angular_nf_primitive_entry_hasDerivAt v lambda s hsl)

theorem angular_nf_integrand_parameter_hasDerivAt (v : Fin 6 → ℂ) (lambda s : ℂ)
    (hl0 : lambda ≠ 0) (hs0 : s ≠ 0) (hsl : s ≠ lambda) (hb : ‖lambda/s‖ < 1) :
    HasDerivAt (fun z => angularNFIntegrand v z s)
      (lambda⁻¹ * angularTensorPair
        (lambda • angularNFParameterDerivative v lambda s +
          angularNFRow v lambda s * nativeEulerConnection (lambda/s))
        (nativeState s) (nativeState (lambda/s))) lambda := by
  have hZ := angular_native_second_parameter_hasDerivAt lambda s hl0 hs0 hb
  have h := angular_tensor_pair_hasDerivAt (fun z => angularNFRow v z s)
    (angularNFParameterDerivative v lambda s) (fun _ => nativeState s)
    (fun z => nativeState (z/s)) 0 _ lambda
    (angular_nf_parameter_entry_hasDerivAt v lambda s hsl)
    (hasDerivAt_const lambda (nativeState s)) hZ
  apply h.congr_deriv
  rw [angular_tensor_pair_add, angular_tensor_pair_smul, angular_tensor_pair_right]
  simp [angularTensorPair, smul_eq_mul, Fin.sum_univ_succ]
  field_simp [hl0]

theorem angular_nf_actual_euler_action (v : Fin 6 → ℂ) (lambda s : ℂ)
    (hl0 : lambda ≠ 0) (hl1 : lambda ≠ 1) (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) (hsl : s ≠ lambda) (hs : ‖s‖ < 1) (hb : ‖lambda/s‖ < 1) :
    lambda * deriv (fun z => angularNFIntegrand v z s) lambda =
      angularNFIntegrand (Matrix.vecMul v (sixthB6 lambda)) lambda s +
        deriv (angularNFPrimitive v lambda) s := by
  rw [(angular_nf_integrand_parameter_hasDerivAt v lambda s hl0 hs0 hsl hb).deriv,
    (angular_nf_primitive_hasDerivAt v lambda s hl0 hs0 hsl hs hb).deriv]
  rw [← mul_assoc, mul_inv_cancel₀ hl0, one_mul,
    angular_nf_euler_action v lambda s hs0 hs1 hsl hl1,
    angular_tensor_pair_add, angular_tensor_pair_add]
  simp only [angularNFIntegrand, add_assoc]

theorem angular_anchor_primitive_hasDerivAt (lambda s : ℂ) (hl0 : lambda ≠ 0)
    (hs0 : s ≠ 0) (hs : ‖s‖ < 1) (hb : ‖lambda/s‖ < 1) :
    HasDerivAt (angularAnchorPrimitive lambda)
      (angularTensorPair (angularRowSAction angularAnchorRow lambda s)
        (nativeState s) (nativeState (lambda/s))) s := by
  change HasDerivAt
    (fun z => angularTensorPair angularAnchorRow (nativeState z) (nativeState (lambda/z))) _ s
  have h := angular_native_pair_s_hasDerivAt (fun _ => angularAnchorRow) 0 lambda s
    hl0 hs0 hs hb (fun i j => hasDerivAt_const s (angularAnchorRow i j))
  simpa only [angularAnchorPrimitive, angularTensorPair, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add] using h

theorem angular_nf_actual_anchor (lambda s : ℂ) (hl0 : lambda ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ lambda)
    (hs : ‖s‖ < 1) (hb : ‖lambda/s‖ < 1) :
    nativeF s * nativeF (lambda/s) / s =
      angularNFIntegrand (sixthCyclicMatrix 0) lambda s +
        deriv (angularAnchorPrimitive lambda) s := by
  rw [(angular_anchor_primitive_hasDerivAt lambda s hl0 hs0 hs hb).deriv]
  have h := congrArg (fun R => angularTensorPair R (nativeState s) (nativeState (lambda/s)))
    (angular_nf_anchor lambda s hs0 hs1 hsl)
  rw [angular_tensor_pair_add] at h
  simpa [angularHolomorphicRow, angularTensorPair, nativeState, Fin.sum_univ_succ,
    angularNFIntegrand, div_eq_mul_inv, mul_comm, mul_left_comm] using h

theorem angular_six_integrands_formula (lambda s : ℂ) :
    angularSixIntegrands lambda s =
      ![dotProduct angularNFWeight (nativeState s) * nativeState (lambda/s) 0 / (s-1),
        dotProduct angularNFWeight (nativeState s) * nativeState (lambda/s) 1 / (s-1),
        dotProduct angularNFWeight (nativeState s) * nativeState (lambda/s) 2 / (s-1),
        nativeState s 0 * dotProduct angularNFWeight (nativeState (lambda/s)) / (s-lambda),
        nativeState s 1 * dotProduct angularNFWeight (nativeState (lambda/s)) / (s-lambda),
        nativeState s 2 * dotProduct angularNFWeight (nativeState (lambda/s)) / (s-lambda)] := by
  ext k
  fin_cases k <;>
    simp [angularSixIntegrands, angular_nf_integrand_formula, angularNFFirst,
      angularNFSecond, dotProduct, Fin.sum_univ_succ]

theorem angular_nf_integrand_linear (v : Fin 6 → ℂ) (lambda s : ℂ) :
    angularNFIntegrand v lambda s = dotProduct v (angularSixIntegrands lambda s) := by
  rw [angular_nf_integrand_formula, angular_six_integrands_formula]
  simp [angularNFFirst, angularNFSecond, dotProduct, Fin.sum_univ_succ,
    div_eq_mul_inv]
  ring

theorem angular_cyclic_row_action (j : Fin 5) (lambda : ℂ) (hl1 : lambda ≠ 1) :
    Matrix.vecMul (sixthCyclicMatrix j.castSucc) (sixthB6 lambda) =
      sixthCyclicMatrix j.succ := by
  ext k
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ => M j.castSucc k)
    (sixth_cyclic_frame lambda hl1)
  fin_cases j <;>
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, sixthCompanion,
      Fin.sum_univ_succ] using h

theorem angular_nf_actual_cyclic_action (j : Fin 5) (lambda s : ℂ)
    (hl0 : lambda ≠ 0) (hl1 : lambda ≠ 1) (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) (hsl : s ≠ lambda) (hs : ‖s‖ < 1) (hb : ‖lambda/s‖ < 1) :
    lambda * deriv (fun z => angularNFIntegrand (sixthCyclicMatrix j.castSucc) z s) lambda =
      angularNFIntegrand (sixthCyclicMatrix j.succ) lambda s +
        deriv (angularNFPrimitive (sixthCyclicMatrix j.castSucc) lambda) s := by
  rw [angular_nf_actual_euler_action (sixthCyclicMatrix j.castSucc)
    lambda s hl0 hl1 hs0 hs1 hsl hs hb, angular_cyclic_row_action j lambda hl1]

end Row12

#print axioms Row12.angular_nf_parameter_entry_hasDerivAt
#print axioms Row12.angular_nf_primitive_entry_hasDerivAt
#print axioms Row12.angular_nf_anchor
#print axioms Row12.angular_nf_euler_action
#print axioms Row12.angular_tensor_pair_add
#print axioms Row12.angular_tensor_pair_smul
#print axioms Row12.angular_tensor_pair_left
#print axioms Row12.angular_tensor_pair_right
#print axioms Row12.angular_tensor_pair_hasDerivAt
#print axioms Row12.angular_nf_integrand_formula
#print axioms Row12.angular_native_second_s_hasDerivAt
#print axioms Row12.angular_native_second_parameter_hasDerivAt
#print axioms Row12.angular_tensor_pair_s_action
#print axioms Row12.angular_native_pair_s_hasDerivAt
#print axioms Row12.angular_nf_primitive_hasDerivAt
#print axioms Row12.angular_nf_integrand_parameter_hasDerivAt
#print axioms Row12.angular_nf_actual_euler_action
#print axioms Row12.angular_anchor_primitive_hasDerivAt
#print axioms Row12.angular_nf_actual_anchor
#print axioms Row12.angular_six_integrands_formula
#print axioms Row12.angular_nf_integrand_linear
#print axioms Row12.angular_cyclic_row_action
#print axioms Row12.angular_nf_actual_cyclic_action
