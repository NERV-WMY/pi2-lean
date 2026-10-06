import Row12.AngularBridge
import Row12.OuterEndpoint

open Filter Matrix

namespace Row12

theorem coefficient3_sq_succ_mul (n : ℕ) :
    ((n : ℝ)+1)^6 * coefficient3 (n+1)^2 =
      ((n : ℝ)+1/6)^2 * ((n : ℝ)+1/2)^2 * ((n : ℝ)+5/6)^2 * coefficient3 n^2 := by
  have hc := coefficient3_succ_mul n
  calc
    _ = (((n : ℝ)+1)^3*coefficient3 (n+1))^2 := by ring
    _ = _ := by rw [hc]; ring

theorem sixthPolynomial_expansion (z : ℂ) :
    (z+1/6)^2*(z+1/2)^2*(z+5/6)^2 =
      z^6+3*z^5+(127/36)*z^4+(37/18)*z^3+(799/1296)*z^2+
        (115/1296)*z+25/5184 := by ring

theorem squaredNativeEuler_sixth (q : ℂ) (hq : ‖q‖ < 1) :
    squaredNativeEuler 6 q = q*(squaredNativeEuler 6 q+3*squaredNativeEuler 5 q+
      (127/36)*squaredNativeEuler 4 q+(37/18)*squaredNativeEuler 3 q+
      (799/1296)*squaredNativeEuler 2 q+(115/1296)*squaredNativeEuler 1 q+
      (25/5184)*squaredNativeEuler 0 q) := by
  have h0 := squaredNativeEuler_summable 0 q hq
  have h1 := squaredNativeEuler_summable 1 q hq
  have h2 := squaredNativeEuler_summable 2 q hq
  have h3 := squaredNativeEuler_summable 3 q hq
  have h4 := squaredNativeEuler_summable 4 q hq
  have h5 := squaredNativeEuler_summable 5 q hq
  have h6 := squaredNativeEuler_summable 6 q hq
  have hshift := h6.tsum_eq_zero_add
  simp only [Nat.cast_zero, zero_pow (by norm_num : 6 ≠ 0), mul_zero, zero_mul,
    zero_add] at hshift
  calc
    squaredNativeEuler 6 q = ∑' n : ℕ, (coefficient3 (n+1) : ℂ)^2*(n+1 : ℂ)^6*q^(n+1) := by
      simpa only [squaredNativeEuler, Nat.cast_add, Nat.cast_one] using hshift
    _ = q*∑' n : ℕ, (coefficient3 n : ℂ)^2*((n : ℂ)+1/6)^2*
        ((n : ℂ)+1/2)^2*((n : ℂ)+5/6)^2*q^n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      have hc : ((n : ℂ)+1)^6*(coefficient3 (n+1) : ℂ)^2 =
          ((n : ℂ)+1/6)^2*((n : ℂ)+1/2)^2*((n : ℂ)+5/6)^2*(coefficient3 n : ℂ)^2 := by
        have hc := congrArg (fun x : ℝ => (x : ℂ)) (coefficient3_sq_succ_mul n)
        push_cast at hc
        exact hc
      calc
        _ = q*((((n : ℂ)+1)^6*(coefficient3 (n+1) : ℂ)^2)*q^n) := by
          rw [pow_succ]
          ring
        _ = _ := by rw [hc]; ring
    _ = _ := by
      congr 1
      have hs := ((((((h6.hasSum.add (h5.hasSum.mul_left 3)).add
        (h4.hasSum.mul_left (127/36))).add (h3.hasSum.mul_left (37/18))).add
        (h2.hasSum.mul_left (799/1296))).add (h1.hasSum.mul_left (115/1296))).add
        (h0.hasSum.mul_left (25/5184)))
      apply HasSum.tsum_eq
      apply hs.congr_fun
      intro n
      simp only [pow_one, pow_zero, mul_one]
      have hp := sixthPolynomial_expansion (n : ℂ)
      linear_combination -((coefficient3 n : ℂ)^2*q^n)*hp

noncomputable def squaredNativeThetaIterate : ℕ → ℂ → ℂ
  | 0 => squaredNativeEuler 0
  | k+1 => nativeTheta (squaredNativeThetaIterate k)

theorem squaredNativeThetaIterate_eq (k : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    squaredNativeThetaIterate k q = squaredNativeEuler k q := by
  induction k generalizing q with
  | zero => rfl
  | succ k hk =>
    have he : squaredNativeThetaIterate k =ᶠ[nhds q] squaredNativeEuler k := by
      have hb : Metric.ball (0 : ℂ) 1 ∈ nhds q :=
        Metric.isOpen_ball.mem_nhds (by simpa using hq)
      filter_upwards [hb] with z hz
      exact hk z (by simpa using hz)
    rw [squaredNativeThetaIterate, nativeTheta, he.deriv_eq,
      ← squaredNativeEuler_succ_eq k q hq]

theorem squaredNative_actualSixthODE (q : ℂ) (hq : ‖q‖ < 1) :
    squaredNativeThetaIterate 6 q = q*(squaredNativeThetaIterate 6 q+
      3*squaredNativeThetaIterate 5 q+(127/36)*squaredNativeThetaIterate 4 q+
      (37/18)*squaredNativeThetaIterate 3 q+(799/1296)*squaredNativeThetaIterate 2 q+
      (115/1296)*squaredNativeThetaIterate 1 q+(25/5184)*squaredNativeThetaIterate 0 q) := by
  simp only [squaredNativeThetaIterate_eq 6 q hq, squaredNativeThetaIterate_eq 5 q hq,
    squaredNativeThetaIterate_eq 4 q hq, squaredNativeThetaIterate_eq 3 q hq,
    squaredNativeThetaIterate_eq 2 q hq, squaredNativeThetaIterate_eq 1 q hq,
    squaredNativeThetaIterate_eq 0 q hq]
  exact squaredNativeEuler_sixth q hq

noncomputable def sixthShift (a : ℂ) (f : ℂ → ℂ) (q : ℂ) : ℂ :=
  nativeTheta f q+a*f q

noncomputable def sixthEulerCombination (v : Fin 7 → ℂ) (q : ℂ) : ℂ :=
  ∑ i : Fin 7, v i*squaredNativeEuler i q

theorem sixthShift_eventually_congr {f g : ℂ → ℂ} {q : ℂ} (a : ℂ)
    (he : f =ᶠ[nhds q] g) : sixthShift a f =ᶠ[nhds q] sixthShift a g := by
  filter_upwards [he, he.deriv] with z hz hdz
  simp only [sixthShift, nativeTheta, hz, hdz]

theorem sixthShift_combination (a : ℂ) (v : Fin 7 → ℂ) (q : ℂ) (hq : ‖q‖ < 1) :
    sixthShift a (sixthEulerCombination v) q =
      (∑ i : Fin 7, v i*squaredNativeEuler (i.val+1) q)+a*sixthEulerCombination v q := by
  have hd : HasDerivAt (sixthEulerCombination v)
      (∑ i : Fin 7, v i*deriv (squaredNativeEuler i) q) q :=
    HasDerivAt.fun_sum (fun i _ =>
      (squaredNativeEuler_analyticAt i q hq).differentiableAt.hasDerivAt.const_mul (v i))
  rw [sixthShift, nativeTheta, hd.deriv, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [squaredNativeEuler_succ_eq i q hq]
  ring

noncomputable def squaredNativeSixthShift : ℂ → ℂ :=
  sixthShift (1/6) (sixthShift (1/6) (sixthShift (1/2) (sixthShift (1/2)
    (sixthShift (5/6) (sixthShift (5/6) (squaredNativeEuler 0))))))

theorem squaredNativeSixthShift_expansion (q : ℂ) (hq : ‖q‖ < 1) :
    squaredNativeSixthShift q = squaredNativeEuler 6 q+3*squaredNativeEuler 5 q+
      (127/36)*squaredNativeEuler 4 q+(37/18)*squaredNativeEuler 3 q+
      (799/1296)*squaredNativeEuler 2 q+(115/1296)*squaredNativeEuler 1 q+
      (25/5184)*squaredNativeEuler 0 q := by
  let v0 : Fin 7 → ℂ := ![1,0,0,0,0,0,0]
  let v1 : Fin 7 → ℂ := ![5/6,1,0,0,0,0,0]
  let v2 : Fin 7 → ℂ := ![25/36,5/3,1,0,0,0,0]
  let v3 : Fin 7 → ℂ := ![25/72,55/36,13/6,1,0,0,0]
  let v4 : Fin 7 → ℂ := ![25/144,10/9,47/18,8/3,1,0,0]
  let v5 : Fin 7 → ℂ := ![25/864,155/432,167/108,55/18,17/6,1,0]
  let v6 : Fin 7 → ℂ := ![25/5184,115/1296,799/1296,37/18,127/36,3,1]
  have hstep (a : ℂ) (v w : Fin 7 → ℂ)
      (hev : ∀ z : ℂ, (∑ i : Fin 7, v i*squaredNativeEuler (i.val+1) z)+
        a*sixthEulerCombination v z = sixthEulerCombination w z) :
      sixthShift a (sixthEulerCombination v) =ᶠ[nhds q] sixthEulerCombination w := by
    have hb : Metric.ball (0 : ℂ) 1 ∈ nhds q :=
      Metric.isOpen_ball.mem_nhds (by simpa using hq)
    filter_upwards [hb] with z hz
    rw [sixthShift_combination a v z (by simpa using hz)]
    exact hev z
  have h01 := hstep (5/6) v0 v1 (by intro z; simp [sixthEulerCombination,v0,v1,Fin.sum_univ_succ]; ring)
  have h12 := hstep (5/6) v1 v2 (by intro z; simp [sixthEulerCombination,v1,v2,Fin.sum_univ_succ]; ring)
  have h23 := hstep (1/2) v2 v3 (by intro z; simp [sixthEulerCombination,v2,v3,Fin.sum_univ_succ]; ring)
  have h34 := hstep (1/2) v3 v4 (by intro z; simp [sixthEulerCombination,v3,v4,Fin.sum_univ_succ]; ring)
  have h45 := hstep (1/6) v4 v5 (by intro z; simp [sixthEulerCombination,v4,v5,Fin.sum_univ_succ]; ring)
  have h56 := hstep (1/6) v5 v6 (by intro z; simp [sixthEulerCombination,v5,v6,Fin.sum_univ_succ]; ring)
  have h0 : squaredNativeEuler 0 =ᶠ[nhds q] sixthEulerCombination v0 := by
    filter_upwards [] with z
    simp [sixthEulerCombination,v0,Fin.sum_univ_succ]
  have h1 := (sixthShift_eventually_congr (5/6) h0).trans h01
  have h2 := (sixthShift_eventually_congr (5/6) h1).trans h12
  have h3 := (sixthShift_eventually_congr (1/2) h2).trans h23
  have h4 := (sixthShift_eventually_congr (1/2) h3).trans h34
  have h5 := (sixthShift_eventually_congr (1/6) h4).trans h45
  have h6 := (sixthShift_eventually_congr (1/6) h5).trans h56
  rw [show squaredNativeSixthShift q = sixthEulerCombination v6 q from h6.self_of_nhds]
  simp [sixthEulerCombination,v6,Fin.sum_univ_succ]
  ring

theorem squaredNative_factoredSixthODE (q : ℂ) (hq : ‖q‖ < 1) :
    squaredNativeThetaIterate 6 q = q*squaredNativeSixthShift q := by
  rw [squaredNativeThetaIterate_eq 6 q hq, squaredNativeSixthShift_expansion q hq]
  exact squaredNativeEuler_sixth q hq

/-- The exact rational C already fixed in OuterEndpoint, transported to the complex field. -/
noncomputable def sixthCyclicMatrix : Matrix (Fin 6) (Fin 6) ℂ :=
  outerCyclicMatrix.map (algebraMap ℚ ℂ)

/-- Literal frozen s08(8) in its six-coordinate order. -/
noncomputable def sixthB6 (q : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0,1,0,0,0,0;
      0,0,1,0,0,0;
      5*q/(72*(1-q)),23*q/(36*(1-q)),3*q/(2*(1-q)),
        -5*q/(72*(1-q)),-23*q/(36*(1-q)),-3*q/(2*(1-q));
      0,0,0,0,1,0;
      0,0,0,0,0,1;
      -5/(72*(1-q)),-23/(36*(1-q)),-3/(2*(1-q)),
        5*q/(72*(1-q)),23*q/(36*(1-q)),3*q/(2*(1-q))]

noncomputable def sixthCompanion (q : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0,1,0,0,0,0;
      0,0,1,0,0,0;
      0,0,0,1,0,0;
      0,0,0,0,1,0;
      0,0,0,0,0,1;
      (25/5184)*q/(1-q),(115/1296)*q/(1-q),(799/1296)*q/(1-q),
        (37/18)*q/(1-q),(127/36)*q/(1-q),3*q/(1-q)]

theorem sixth_cyclic_frame (q : ℂ) (hq : q ≠ 1) :
    sixthCyclicMatrix*sixthB6 q = sixthCompanion q*sixthCyclicMatrix := by
  have hd : 1-q ≠ 0 := sub_ne_zero.mpr hq.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixthCyclicMatrix, outerCyclicMatrix, sixthB6, sixthCompanion,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply] <;>
    field_simp [hd] <;> ring

noncomputable def sixthCyclicInverse : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0,0,0,-1,0,0;
      0,0,0,0,-1,0;
      0,0,0,0,0,-1;
      5/72,23/36,3/2,1,0,0;
      0,5/72,23/36,3/2,1,0;
      0,0,5/72,23/36,3/2,1]

theorem sixth_cyclic_inverse_left : sixthCyclicInverse*sixthCyclicMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixthCyclicInverse, sixthCyclicMatrix, outerCyclicMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply]

theorem sixth_cyclic_inverse_right : sixthCyclicMatrix*sixthCyclicInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixthCyclicInverse, sixthCyclicMatrix, outerCyclicMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply]

noncomputable def sixthState (q : ℂ) : Fin 6 → ℂ :=
  ![squaredNativeEuler 0 q,squaredNativeEuler 1 q,squaredNativeEuler 2 q,
    squaredNativeEuler 3 q,squaredNativeEuler 4 q,squaredNativeEuler 5 q]

noncomputable def sixthNormalState (q : ℂ) : Fin 6 → ℂ :=
  sixthCyclicInverse.mulVec (sixthState q)

theorem sixth_state_companion (q : ℂ) (hq : ‖q‖ < 1) :
    (fun i : Fin 6 => q*deriv (fun z => sixthState z i) q) =
      (sixthCompanion q).mulVec (sixthState q) := by
  have hq1 : q ≠ 1 := by intro he; simp [he] at hq
  have hd : 1-q ≠ 0 := sub_ne_zero.mpr hq1.symm
  have hs := squaredNativeEuler_sixth q hq
  ext i
  fin_cases i
  · simpa [sixthState,sixthCompanion,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      using (squaredNativeEuler_succ_eq 0 q hq).symm
  · simpa [sixthState,sixthCompanion,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      using (squaredNativeEuler_succ_eq 1 q hq).symm
  · simpa [sixthState,sixthCompanion,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      using (squaredNativeEuler_succ_eq 2 q hq).symm
  · simpa [sixthState,sixthCompanion,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      using (squaredNativeEuler_succ_eq 3 q hq).symm
  · simpa [sixthState,sixthCompanion,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      using (squaredNativeEuler_succ_eq 4 q hq).symm
  · change q*deriv (squaredNativeEuler 5) q = _
    rw [← squaredNativeEuler_succ_eq 5 q hq]
    have he : squaredNativeEuler 6 q =
        (q*(3*squaredNativeEuler 5 q+(127/36)*squaredNativeEuler 4 q+
          (37/18)*squaredNativeEuler 3 q+(799/1296)*squaredNativeEuler 2 q+
          (115/1296)*squaredNativeEuler 1 q+(25/5184)*squaredNativeEuler 0 q))/(1-q) :=
      (eq_div_iff hd).2 (by linear_combination hs)
    rw [he]
    simp [sixthState,sixthCompanion,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring

theorem sixth_state_analyticAt (i : Fin 6) (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (fun z => sixthState z i) q := by
  fin_cases i <;> change AnalyticAt ℂ (squaredNativeEuler _) q <;>
    exact squaredNativeEuler_analyticAt _ q hq

theorem sixth_inverse_frame (q : ℂ) (hq : q ≠ 1) :
    sixthCyclicInverse*sixthCompanion q = sixthB6 q*sixthCyclicInverse := by
  calc
    _ = (sixthCyclicInverse*sixthCompanion q)*(sixthCyclicMatrix*sixthCyclicInverse) := by
      rw [sixth_cyclic_inverse_right, Matrix.mul_one]
    _ = (sixthCyclicInverse*(sixthCompanion q*sixthCyclicMatrix))*sixthCyclicInverse := by
      simp only [Matrix.mul_assoc]
    _ = (sixthCyclicInverse*(sixthCyclicMatrix*sixthB6 q))*sixthCyclicInverse := by
      rw [sixth_cyclic_frame q hq]
    _ = _ := by rw [← Matrix.mul_assoc, sixth_cyclic_inverse_left, Matrix.one_mul]

theorem sixth_normal_state_equation (q : ℂ) (hq : ‖q‖ < 1) :
    (fun i : Fin 6 => q*deriv (fun z => sixthNormalState z i) q) =
      (sixthB6 q).mulVec (sixthNormalState q) := by
  have hq1 : q ≠ 1 := by intro he; simp [he] at hq
  have hd (i : Fin 6) : HasDerivAt (fun z => sixthNormalState z i)
      (∑ j : Fin 6, sixthCyclicInverse i j*deriv (fun z => sixthState z j) q) q := by
    unfold sixthNormalState Matrix.mulVec dotProduct
    apply HasDerivAt.fun_sum
    intro j _
    exact (sixth_state_analyticAt j q hq).differentiableAt.hasDerivAt.const_mul
      (sixthCyclicInverse i j)
  calc
    _ = sixthCyclicInverse.mulVec (fun j : Fin 6 => q*deriv (fun z => sixthState z j) q) := by
      ext i
      rw [(hd i).deriv]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = sixthCyclicInverse.mulVec ((sixthCompanion q).mulVec (sixthState q)) := by
      rw [sixth_state_companion q hq]
    _ = (sixthCyclicInverse*sixthCompanion q).mulVec (sixthState q) :=
      Matrix.mulVec_mulVec _ _ _
    _ = (sixthB6 q*sixthCyclicInverse).mulVec (sixthState q) := by
      rw [sixth_inverse_frame q hq1]
    _ = (sixthB6 q).mulVec (sixthNormalState q) := by
      rw [← Matrix.mulVec_mulVec]
      rfl

end Row12

#print axioms Row12.coefficient3_sq_succ_mul
#print axioms Row12.sixthPolynomial_expansion
#print axioms Row12.squaredNativeEuler_sixth
#print axioms Row12.squaredNativeThetaIterate_eq
#print axioms Row12.squaredNative_actualSixthODE
#print axioms Row12.sixthShift_eventually_congr
#print axioms Row12.sixthShift_combination
#print axioms Row12.squaredNativeSixthShift_expansion
#print axioms Row12.squaredNative_factoredSixthODE
#print axioms Row12.sixth_cyclic_frame
#print axioms Row12.sixth_cyclic_inverse_left
#print axioms Row12.sixth_cyclic_inverse_right
#print axioms Row12.sixth_state_companion
#print axioms Row12.sixth_state_analyticAt
#print axioms Row12.sixth_inverse_frame
#print axioms Row12.sixth_normal_state_equation
