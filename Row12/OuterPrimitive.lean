import Row12.SixthSeries

open Filter Matrix

namespace Row12

noncomputable def outerPrimitiveBasis (x : ℂ) : Fin 15 → ℂ :=
  ![1/x,1/x^2,1/x^3,1/x^4,1/(99*x-50),1/(99*x-50)^2,
    1,x,x^2,x^3,x^4,x^5,x^6,x^7,x^8]

noncomputable def outerPrimitiveBasisDerivative (x : ℂ) : Fin 15 → ℂ :=
  ![-1/x^2,-2/x^3,-3/x^4,-4/x^5,-99/(99*x-50)^2,-198/(99*x-50)^3,
    0,1,2*x,3*x^2,4*x^3,5*x^4,6*x^5,7*x^6,8*x^7]

/-- All 90 literal s14 primitive coefficients, in the displayed basis order. -/
noncomputable def outerPrimitiveCoefficients : Matrix (Fin 15) (Fin 6) ℂ :=
  !![    105800/459459,867560/459459,103229200/459459,-169280/51051,-1388096/51051,-2268352/51051;
    0,0,-472485400/459459,0,0,0;
    0,0,338560000/196911,0,0,0;
    0,0,-4232000000/4135131,0,0,0;
    -78890805485931260/886402053948411,-1227125311357021190/886402053948411,-70427029255928891500/6204814377638877,-607873567055897705440/74327471429736107583,-298973396640778498112/8258607936637345287,-145365088004028281168/635277533587488099;
    -231954922267076000/229807939912551,-331597299956488000/76602646637517,-108998157631733600/5892511279809,-39913346954892419000/917623104070816143,28252939480465998800/101958122674535127,-14427468858797595200/5997536627913831;
    -44128649359258592/31024071888194385,623049674458568524/31024071888194385,6660655461825680912/31024071888194385,57598947351747925330/10618210204248015369,370356988491186478316/8258607936637345287,422172179336846381488/5899005669026675205;
    7410960991604618219/7834361587927875000,-2244024947258679397/230422399644937500,-8368444588355333518/75330399883921875,-1674067760127596905471/469239087308940073125,-7571431721389433993041/260688381838300040625,-60217890176084166521579/1303441909191500203125;
    -1014783336398633/79134965534625000,99347762374288343/39567482767312500,226386615454772638/9891870691828125,1399948922915894608/4739788760696364375,6901571092120745041/2633215978164646875,59461141531221275693/13166079890823234375;
    -1051211136/19184234069,-440067361152/479605851725,-18358156683264/2398029258625,1031881871061389312/1196916353711203125,258130738760714016/40711440602421875,20750847913747165488/1994860589518671875;
    1029377673/34880425580,430927242561/872010639500,4494215281788/1090013299375,-250759381828805733/558002962103125000,-14957478836244716238/4533774067087890625,-24572653010256580956/4533774067087890625;
    -16224867/3170947780,-6792198219/79273694500,-70837018452/99092118125,300193629643629927/3297290230609375000,1380547922050429344/2060806394130859375,2261266906791518928/2060806394130859375;
    0,0,0,-223303109482368/7493841433203125,-8431993935111168/37469207166015625,-13467359214383616/37469207166015625;
    0,0,0,218665144746549/13625166242187500,2064215740879206/17031457802734375,3296911156760547/17031457802734375;
    0,0,0,-3446560950471/1238651476562500,-32535799768674/1548314345703125,-51965324712513/1548314345703125]

/-- Literal s12 six_coordinate_source, in frozen first-three/last-three order. -/
noncomputable def outerSourceRow (x : ℂ) : Fin 6 → ℂ :=
  ![-(49911735537576000 * x^10 - 358366114625568750 * x^9 + 1024896781084880250 * x^8 - 1504649505484526625 * x^7 + 452996231267528739 * x^6 - 967095462947044050 * x^5 + 4568259094506607500 * x^4 - 6390265799696625000 * x^3 + 4776671745037500000 * x^2 - 1620026581250000000 * x + 203665000000000000)/(884458575000 * x^2 * (99 * x - 50)^3),
    -(424991536633320525 * x^10 - 3059269893497952675 * x^9 + 8776295385209831250 * x^8 - 17980716578328028350 * x^7 + 40033847500084452231 * x^6 - 72681314187914929575 * x^5 + 72991314248116398750 * x^4 - 42274489174403062500 * x^3 + 20412363692634375000 * x^2 - 6742838987500000000 * x + 835026500000000000)/(442229287500 * x^2 * (99 * x - 50)^3),
    -(16254637002555354315 * x^13 - 117331289817565846140 * x^12 + 337708827799074815355 * x^11 - 712568763360020254725 * x^10 + 1748175772637166704388 * x^9 - 3284853027606881257275 * x^8 + 3704502474256540713750 * x^7 - 9155313050168474437500 * x^6 + 35764645331938415625000 * x^5 - 76328567295533437500000 * x^4 + 86614239637406250000000 * x^3 - 52943748309375000000000 * x^2 + 16445948750000000000000 * x - 2036650000000000000000)/(1990031793750 * x^5 * (99 * x - 50)^3),
    -(1985653292967065304 * x^13 - 14368114735064950374 * x^12 + 41475305233234945818 * x^11 - 88343270723508495705 * x^10 + 221167038990204750141 * x^9 - 423533970403323140880 * x^8 + 474160356450500328000 * x^7 - 968138785177596900000 * x^6 + 3581908522999976250000 * x^5 - 7627707731215687500000 * x^4 + 8660787001453125000000 * x^3 - 5294374830937500000000 * x^2 + 1644594875000000000000 * x - 203665000000000000000)/(61420734375000 * x^2 * (99 * x - 50)^3),
    -(36543294297940253472 * x^13 - 263435458016134499112 * x^12 + 757044868395948363864 * x^11 - 1569822791226846121485 * x^10 + 3723903857070844049628 * x^9 - 6706460023297782552765 * x^8 + 7104436804434687747750 * x^7 - 18032895993731205825000 * x^6 + 72792768566568622500000 * x^5 - 156236863530002062500000 * x^4 + 177487785902109375000000 * x^3 - 108534684034218750000000 * x^2 + 33714194937500000000000 * x - 4175132500000000000000)/(153551835937500 * x^2 * (99 * x - 50)^3),
    -(14697320943081344436 * x^13 - 106064566372879052661 * x^12 + 305192775314146313547 * x^11 - 642442623371264688075 * x^10 + 1566716945575890250404 * x^9 - 2892773628120033493245 * x^8 + 3118878132004496822625 * x^7 - 7639960648920801665625 * x^6 + 30095841001386345468750 * x^5 - 64187382415999992187500 * x^4 + 72733992740694140625000 * x^3 - 44373556405664062500000 * x^2 + 13773482078125000000000 * x - 1705694375000000000000)/(38387958984375 * x^2 * (99 * x - 50)^3)]


noncomputable def outerPrimitiveRow (x : ℂ) : Fin 6 → ℂ :=
  fun j => ∑ k : Fin 15, outerPrimitiveCoefficients k j*outerPrimitiveBasis x k

noncomputable def outerPrimitiveDerivative (x : ℂ) : Fin 6 → ℂ :=
  fun j => ∑ k : Fin 15, outerPrimitiveCoefficients k j*outerPrimitiveBasisDerivative x k

noncomputable def outerPrimitiveLambda (x : ℂ) : ℂ := (729/15625)*x^3

noncomputable def outerSelectedRow : Fin 6 → ℂ := fun j =>
  9*sixthCyclicMatrix 0 j+180*sixthCyclicMatrix 1 j+
    1288*sixthCyclicMatrix 2 j+3192*sixthCyclicMatrix 3 j

theorem outer_selected_row_eq (j : Fin 6) :
    outerSelectedRow j = 9*(sixthCyclicMatrix 0 j+6*sixthCyclicMatrix 1 j)+
      126*(sixthCyclicMatrix 1 j+6*sixthCyclicMatrix 2 j)+
      532*(sixthCyclicMatrix 2 j+6*sixthCyclicMatrix 3 j) := by
  unfold outerSelectedRow
  ring

theorem outer_selected_row_literal :
    outerSelectedRow = ![108904/125,713232/125,358848/125,648/5,34992/25,358848/125] := by
  ext j
  fin_cases j <;> norm_num [outerSelectedRow,sixthCyclicMatrix,outerCyclicMatrix,
    Matrix.map_apply,Matrix.cons_val_two,Matrix.cons_val_three]

theorem outerInversePower_hasDerivAt (m : ℕ) (x : ℂ) (hx : x ≠ 0) :
    HasDerivAt (fun z : ℂ => 1/z^(m+1)) (-(m+1 : ℂ)/x^(m+2)) x := by
  have hd : HasDerivAt (fun z : ℂ => (z^(m+1))⁻¹)
      (-((m+1 : ℂ)*x^m)/(x^(m+1))^2) x := by
    convert! ((hasDerivAt_id x).pow (m+1)).inv (pow_ne_zero (m+1) hx) using 1
    simp
  have he : -((m+1 : ℂ)*x^m)/(x^(m+1))^2 =
      -(m+1 : ℂ)/x^(m+2) := by
    simp only [pow_succ]
    field_simp [hx]
  convert! hd.congr_deriv he using 1
  funext z
  exact one_div (z^(m+1))

theorem outerAffineInversePower_hasDerivAt (m : ℕ) (x : ℂ) (hx : 99*x-50 ≠ 0) :
    HasDerivAt (fun z : ℂ => 1/(99*z-50)^(m+1))
      (-(99*(m+1 : ℂ))/(99*x-50)^(m+2)) x := by
  have ha := ((hasDerivAt_id x).const_mul 99).sub_const 50
  have hd := (outerInversePower_hasDerivAt m (99*x-50) hx).comp x ha
  have he : (-(m+1 : ℂ)/(99*x-50)^(m+2))*(99*1) =
      -(99*(m+1 : ℂ))/(99*x-50)^(m+2) := by ring
  convert! hd.congr_deriv he using 1

theorem outer_basis_hasDerivAt (k : Fin 15) (x : ℂ)
    (hx : x ≠ 0) (hE : 99*x-50 ≠ 0) :
    HasDerivAt (fun z => outerPrimitiveBasis z k) (outerPrimitiveBasisDerivative x k) x := by
  fin_cases k
  all_goals dsimp only [outerPrimitiveBasis,outerPrimitiveBasisDerivative]
  · convert! outerInversePower_hasDerivAt 0 x hx using 1
    all_goals norm_num
  · convert! outerInversePower_hasDerivAt 1 x hx using 1
    all_goals norm_num
  · convert! outerInversePower_hasDerivAt 2 x hx using 1
    all_goals norm_num
  · convert! outerInversePower_hasDerivAt 3 x hx using 1
    all_goals norm_num
  · convert! outerAffineInversePower_hasDerivAt 0 x hE using 1
    all_goals norm_num
  · convert! outerAffineInversePower_hasDerivAt 1 x hE using 1
    all_goals norm_num
  · convert! hasDerivAt_const x (1 : ℂ) using 1
  · convert! hasDerivAt_id x using 1
  · convert! (hasDerivAt_id x).pow 2 using 1
    all_goals norm_num
  · convert! (hasDerivAt_id x).pow 3 using 1
    all_goals norm_num
  · convert! (hasDerivAt_id x).pow 4 using 1
    all_goals norm_num
  · convert! (hasDerivAt_id x).pow 5 using 1
    all_goals norm_num
  · convert! (hasDerivAt_id x).pow 6 using 1
    all_goals norm_num
  · convert! (hasDerivAt_id x).pow 7 using 1
    all_goals norm_num
  · convert! (hasDerivAt_id x).pow 8 using 1
    all_goals norm_num

theorem outer_primitive_hasDerivAt (j : Fin 6) (x : ℂ)
    (hx : x ≠ 0) (hE : 99*x-50 ≠ 0) :
    HasDerivAt (fun z => outerPrimitiveRow z j) (outerPrimitiveDerivative x j) x :=
  HasDerivAt.fun_sum (fun k _ => (outer_basis_hasDerivAt k x hx hE).const_mul
    (outerPrimitiveCoefficients k j))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
 theorem outer_rational_row_identity (x : ℂ) (hx : x ≠ 0)
    (hE : 99*x-50 ≠ 0) (hL : outerPrimitiveLambda x ≠ 1) (j : Fin 6) :
    outerSourceRow x j-outerSelectedRow j/3375 =
      outerPrimitiveRow x j-2*(1-x)*outerPrimitiveDerivative x j-
        (6*(1-x)/x)*(Matrix.vecMul (outerPrimitiveRow x) (sixthB6 (outerPrimitiveLambda x))) j := by
  have hd : 1-(729/15625 : ℂ)*x^3 ≠ 0 := by
    simpa only [outerPrimitiveLambda] using (sub_ne_zero.mpr hL.symm)
  fin_cases j
  all_goals
    simp only [outerSourceRow,outer_selected_row_literal,outerPrimitiveRow,outerPrimitiveDerivative,
      outerPrimitiveCoefficients,outerPrimitiveBasis,outerPrimitiveBasisDerivative,
      sixthB6,outerPrimitiveLambda,Matrix.vecMul,dotProduct,Fin.sum_univ_succ,
      Matrix.cons_val_zero,Matrix.cons_val_succ]
    norm_num only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,
      Fin.sum_univ_zero]
    generalize he : 99*x-50 = e at hE ⊢
    generalize hD : 1-(729/15625 : ℂ)*x^3 = d at hd ⊢
    norm_num
    field_simp [hx,hE,hd]
    rw [← he,← hD]
    ring

theorem outer_rational_connection_identity (x : ℂ) (hx : x ≠ 0)
    (hx1 : x ≠ 1) (hE : 99*x-50 ≠ 0) (hL : outerPrimitiveLambda x ≠ 1) (j : Fin 6) :
    -outerSourceRow x j/(2*(1-x)) = -outerSelectedRow j/(3375*2*(1-x))+
      outerPrimitiveDerivative x j+
      (3/x)*(Matrix.vecMul (outerPrimitiveRow x) (sixthB6 (outerPrimitiveLambda x))) j-
      outerPrimitiveRow x j/(2*(1-x)) := by
  have hd : 1-x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have he := outer_rational_row_identity x hx hE hL j
  symm
  calc
    _ = -(outerPrimitiveRow x j-2*(1-x)*outerPrimitiveDerivative x j-
        (6*(1-x)/x)*(Matrix.vecMul (outerPrimitiveRow x) (sixthB6 (outerPrimitiveLambda x))) j+
        outerSelectedRow j/3375)/(2*(1-x)) := by
      field_simp [hx,hd]
      ring
    _ = _ := by
      congr 1
      linear_combination he

noncomputable def outerPrimitiveFlux (U : ℂ) : ℂ :=
  U*dotProduct (outerPrimitiveRow (1-U^2))
    (sixthNormalState (outerPrimitiveLambda (1-U^2)))

theorem outer_lambda_ne_zero (x : ℂ) (hx : x ≠ 0) : outerPrimitiveLambda x ≠ 0 := by
  unfold outerPrimitiveLambda
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hx)

theorem outer_lambda_path_hasDerivAt (U : ℂ) (hx : 1-U^2 ≠ 0) :
    HasDerivAt (fun z : ℂ => outerPrimitiveLambda (1-z^2))
      (-(6*U)*outerPrimitiveLambda (1-U^2)/(1-U^2)) U := by
  have hX := (hasDerivAt_const U (1 : ℂ)).sub ((hasDerivAt_id U).pow 2)
  have hL := (hX.pow 3).const_mul (729/15625 : ℂ)
  convert! hL using 1
  norm_num [outerPrimitiveLambda,id_eq]
  field_simp [hx]
  ring

theorem outer_normal_state_hasDerivAt (i : Fin 6) (q : ℂ)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    HasDerivAt (fun z => sixthNormalState z i)
      (((sixthB6 q).mulVec (sixthNormalState q)) i/q) q := by
  have hd : HasDerivAt (fun z => sixthNormalState z i)
      (∑ j : Fin 6, sixthCyclicInverse i j*deriv (fun z => sixthState z j) q) q := by
    unfold sixthNormalState Matrix.mulVec dotProduct
    exact HasDerivAt.fun_sum (fun j _ =>
      (sixth_state_analyticAt j q hq).differentiableAt.hasDerivAt.const_mul
        (sixthCyclicInverse i j))
  have he : deriv (fun z => sixthNormalState z i) q =
      (((sixthB6 q).mulVec (sixthNormalState q)) i/q) :=
    (eq_div_iff hq0).2 (by
      simpa only [mul_comm] using congrFun (sixth_normal_state_equation q hq) i)
  exact hd.differentiableAt.hasDerivAt.congr_deriv he

theorem outer_selected_pairing (q : ℂ) :
    dotProduct outerSelectedRow (sixthNormalState q) =
      9*squaredNativeEuler 0 q+180*squaredNativeEuler 1 q+
        1288*squaredNativeEuler 2 q+3192*squaredNativeEuler 3 q := by
  have hf : sixthCyclicMatrix.mulVec (sixthNormalState q) = sixthState q := by
    unfold sixthNormalState
    rw [Matrix.mulVec_mulVec,sixth_cyclic_inverse_right,Matrix.one_mulVec]
  calc
    _ = 9*(sixthCyclicMatrix.mulVec (sixthNormalState q)) 0+
        180*(sixthCyclicMatrix.mulVec (sixthNormalState q)) 1+
        1288*(sixthCyclicMatrix.mulVec (sixthNormalState q)) 2+
        3192*(sixthCyclicMatrix.mulVec (sixthNormalState q)) 3 := by
      simp only [outerSelectedRow,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      ring
    _ = _ := by
      rw [hf]
      simp only [sixthState,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]

theorem outer_rational_pairing_identity (x : ℂ) (hx : x ≠ 0)
    (hE : 99*x-50 ≠ 0) (hL : outerPrimitiveLambda x ≠ 1)
    (v : Fin 6 → ℂ) :
    dotProduct (outerSourceRow x) v-dotProduct outerSelectedRow v/3375 =
      dotProduct (outerPrimitiveRow x) v-
        2*(1-x)*dotProduct (outerPrimitiveDerivative x) v-
        (6*(1-x)/x)*dotProduct (outerPrimitiveRow x)
          ((sixthB6 (outerPrimitiveLambda x)).mulVec v) := by
  rw [Matrix.dotProduct_mulVec]
  have hr : (∑ j : Fin 6, (outerSourceRow x j-outerSelectedRow j/3375)*v j) =
      ∑ j : Fin 6, (outerPrimitiveRow x j-2*(1-x)*outerPrimitiveDerivative x j-
        (6*(1-x)/x)*(Matrix.vecMul (outerPrimitiveRow x)
          (sixthB6 (outerPrimitiveLambda x))) j)*v j :=
    Finset.sum_congr rfl (fun j _ =>
      congrArg (fun t : ℂ => t*v j) (outer_rational_row_identity x hx hE hL j))
  simpa only [dotProduct,sub_mul,div_mul_eq_mul_div,mul_assoc,
    Finset.sum_sub_distrib,Finset.sum_div,Finset.mul_sum] using hr

theorem outer_primitive_flux_hasDerivAt (U : ℂ) (hx : 1-U^2 ≠ 0)
    (hE : 99*(1-U^2)-50 ≠ 0) (hq : ‖outerPrimitiveLambda (1-U^2)‖ < 1) :
    HasDerivAt outerPrimitiveFlux
      (dotProduct (outerSourceRow (1-U^2))
          (sixthNormalState (outerPrimitiveLambda (1-U^2)))-
        (9*squaredNativeEuler 0 (outerPrimitiveLambda (1-U^2))+
          180*squaredNativeEuler 1 (outerPrimitiveLambda (1-U^2))+
          1288*squaredNativeEuler 2 (outerPrimitiveLambda (1-U^2))+
          3192*squaredNativeEuler 3 (outerPrimitiveLambda (1-U^2)))/3375) U := by
  let x := 1-U^2
  let q := outerPrimitiveLambda x
  have hq0 : q ≠ 0 := outer_lambda_ne_zero x hx
  have hq1 : q ≠ 1 := by
    intro he
    have ht : ‖q‖ < 1 := hq
    simp [he] at ht
  have hX : HasDerivAt (fun z : ℂ => 1-z^2) (-2*U) U := by
    convert! (hasDerivAt_const U (1 : ℂ)).sub ((hasDerivAt_id U).pow 2) using 1
    simp only [id_eq]
    ring
  have hA (j : Fin 6) : HasDerivAt
      (fun z => sixthNormalState (outerPrimitiveLambda (1-z^2)) j)
      ((-6*U/x)*((sixthB6 q).mulVec (sixthNormalState q)) j) U := by
    have hL : HasDerivAt (fun z : ℂ => outerPrimitiveLambda (1-z^2))
        (-(6*U)*q/x) U := outer_lambda_path_hasDerivAt U hx
    have ht := (outer_normal_state_hasDerivAt j q hq0 hq).comp U hL
    convert! ht using 1
    field_simp [hq0]
  have hXi (j : Fin 6) : HasDerivAt (fun z => outerPrimitiveRow (1-z^2) j)
      (outerPrimitiveDerivative x j*(-2*U)) U := by
    convert! (outer_primitive_hasDerivAt j (1-U^2) hx hE).comp U hX using 1
  have hD := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 6)))
    (fun j _ => (hXi j).mul (hA j))
  have hF := (hasDerivAt_id U).mul hD
  have he :
      1*(∑ j : Fin 6, outerPrimitiveRow x j*sixthNormalState q j)+
        U*(∑ j : Fin 6, (outerPrimitiveDerivative x j*(-2*U)*sixthNormalState q j+
          outerPrimitiveRow x j*((-6*U/x)*((sixthB6 q).mulVec (sixthNormalState q)) j))) =
      dotProduct (outerSourceRow x) (sixthNormalState q)-
        dotProduct outerSelectedRow (sixthNormalState q)/3375 := by
    rw [outer_rational_pairing_identity x hx hE hq1]
    dsimp only [q,x]
    simp only [dotProduct,Fin.sum_univ_succ]
    ring
  rw [outer_selected_pairing] at he
  exact hF.congr_deriv he

theorem outer_primitive_flux_deriv (U : ℂ) (hx : 1-U^2 ≠ 0)
    (hE : 99*(1-U^2)-50 ≠ 0) (hq : ‖outerPrimitiveLambda (1-U^2)‖ < 1) :
    deriv outerPrimitiveFlux U =
      dotProduct (outerSourceRow (1-U^2))
          (sixthNormalState (outerPrimitiveLambda (1-U^2)))-
        (9*squaredNativeEuler 0 (outerPrimitiveLambda (1-U^2))+
          180*squaredNativeEuler 1 (outerPrimitiveLambda (1-U^2))+
          1288*squaredNativeEuler 2 (outerPrimitiveLambda (1-U^2))+
          3192*squaredNativeEuler 3 (outerPrimitiveLambda (1-U^2)))/3375 :=
  (outer_primitive_flux_hasDerivAt U hx hE hq).deriv

end Row12

#print axioms Row12.outer_selected_row_eq
#print axioms Row12.outer_selected_row_literal
#print axioms Row12.outerInversePower_hasDerivAt
#print axioms Row12.outerAffineInversePower_hasDerivAt
#print axioms Row12.outer_basis_hasDerivAt
#print axioms Row12.outer_primitive_hasDerivAt
#print axioms Row12.outer_rational_row_identity
#print axioms Row12.outer_rational_connection_identity
#print axioms Row12.outer_lambda_ne_zero
#print axioms Row12.outer_lambda_path_hasDerivAt
#print axioms Row12.outer_normal_state_hasDerivAt
#print axioms Row12.outer_selected_pairing
#print axioms Row12.outer_rational_pairing_identity
#print axioms Row12.outer_primitive_flux_hasDerivAt
#print axioms Row12.outer_primitive_flux_deriv
