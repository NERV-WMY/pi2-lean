import Row12.ScalarFlux
import Row12.EscapeNumerator
import Row12.EscapeRemovable

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

theorem scalar_escape_factor_ne_zero {U : ℝ} (hU : 0 < U) (hne : U ≠ escapePoint) :
    99*scalarPathX U-50 ≠ 0 := by
  intro h
  have he := escapePoint_sq
  have hprod : (U-escapePoint)*(U+escapePoint)=0 := by
    unfold scalarPathX at h
    nlinarith
  rcases mul_eq_zero.mp hprod with heq | heq
  · exact hne (sub_eq_zero.mp heq)
  · have hp := escapePoint_mem.1
    linarith

noncomputable def escapeRealNumerator (q : ℝ) : ℝ :=
  (escapeClearedTotal ((escapePoint+q:ℝ):ℂ)).re /
    (9801*(2*escapePoint+q)^2)

theorem escapeRealNumerator_analyticAt : AnalyticAt ℝ escapeRealNumerator 0 := by
  have hc : AnalyticAt ℝ escapeClearedTotal (escapePoint:ℂ) :=
    escapeClearedTotal_analyticAt.restrictScalars
  have hi : AnalyticAt ℝ (fun q : ℝ => ((escapePoint+q:ℝ):ℂ)) 0 := by
    have hh : AnalyticAt ℝ (fun q : ℝ => (escapePoint:ℂ)+Complex.ofRealCLM q) 0 :=
      analyticAt_const.add (Complex.ofRealCLM.analyticAt (0:ℝ))
    simpa only [Complex.ofReal_add,Complex.ofRealCLM_apply] using hh
  have hc0 : AnalyticAt ℝ escapeClearedTotal ((escapePoint+(0:ℝ):ℝ):ℂ) := by
    simpa only [add_zero] using hc
  have ha : AnalyticAt ℝ (fun q : ℝ => (escapeClearedTotal ((escapePoint+q:ℝ):ℂ)).re) 0 :=
    (Complex.reCLM.analyticAt _).comp
      (hc0.comp (f := fun q : ℝ => ((escapePoint+q:ℝ):ℂ)) (x := 0) hi)
  unfold escapeRealNumerator
  exact ha.div (by fun_prop) (by
    have hp := escapePoint_mem.1
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (by linarith)))

theorem escapeRealNumerator_quotient_eventually :
    (fun q : ℝ => escapeRealNumerator q/q^2) =ᶠ[nhdsWithin 0 {0}ᶜ]
      (fun q => scalarTotalFlux (escapePoint+q)) := by
  have hshift : Tendsto (fun q : ℝ => escapePoint+q) (nhds 0) (nhds escapePoint) := by
    have hc : ContinuousAt (fun q : ℝ => escapePoint+q) 0 := by fun_prop
    simpa only [add_zero] using hc.tendsto
  have hshiftC : Tendsto (fun q : ℝ => ((escapePoint+q:ℝ):ℂ))
      (nhds 0) (nhds (escapePoint:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hshift
  have hclear := hshiftC.eventually escapeClearedTotal_clears_near
  have hcompare := hshift.eventually (beta_balanced_fixedCircle_eventually_of_off_pole
    escapePoint_mem.1 escapePoint_mem.2)
  have hinside := hshift.eventually (Ioo_mem_nhds escapePoint_mem.1 escapePoint_mem.2)
  filter_upwards [hclear.filter_mono nhdsWithin_le_nhds,
    hcompare.filter_mono nhdsWithin_le_nhds,hinside.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with q hC hB hI hq
  have hq0 : q ≠ 0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hq
  have hUne : escapePoint+q ≠ escapePoint := by
    intro he
    apply hq0
    linarith
  have hE := scalar_escape_factor_ne_zero hI.1 hUne
  have hEC : escapeFactor ((escapePoint+q:ℝ):ℂ) ≠ 0 := by
    unfold escapeFactor betaFrameX
    exact_mod_cast hE
  have hCC := hC hEC
  have hBB := hB hE
  change betaFluxBalanced (escapePoint+q) =
    betaFluxCircle ((escapePoint+q:ℝ):ℂ) escapeRadius at hBB
  rw [← hBB] at hCC
  have hfactor : escapeFactor ((escapePoint+q:ℝ):ℂ) =
      ((-99*q*(2*escapePoint+q):ℝ):ℂ) := by
    have he := escapePoint_sq
    unfold escapeFactor betaFrameX
    push_cast
    have heC : (escapePoint:ℂ)^2=49/99 := by
      rw [← Complex.ofReal_pow,he]
      norm_num
    linear_combination -99*heC
  have hfactor2 : escapeFactor ((escapePoint+q:ℝ):ℂ)^2 =
      ((9801*q^2*(2*escapePoint+q)^2:ℝ):ℂ) := by
    rw [hfactor]
    push_cast
    ring
  rw [hfactor2] at hCC
  have hr := congrArg Complex.re hCC
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hr
  have hunit : 2*escapePoint+q ≠ 0 := by have hp := escapePoint_mem.1; linarith [hI.1]
  unfold escapeRealNumerator scalarTotalFlux
  rw [hr]
  field_simp [hq0,hunit]

theorem scalarTotalFlux_shift_derivative_limit :
    Tendsto (deriv (fun q : ℝ => scalarTotalFlux (escapePoint+q)))
      (nhdsWithin 0 (Ioi 0)) (nhds (-scalarIntegrand escapePoint/3375)) := by
  have hi : Tendsto (fun q : ℝ => q) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun q : ℝ => escapePoint+q)
      (nhdsWithin 0 (Ioi 0)) (nhds escapePoint) := by
    simpa only [add_zero] using tendsto_const_nhds.add hi
  have hc : ContinuousAt scalarIntegrand escapePoint :=
    scalarIntegrand_continuousOn.continuousAt
      (Icc_mem_nhds escapePoint_mem.1 escapePoint_mem.2)
  have ht := ((hc.tendsto.comp hs).neg).div_const (3375:ℝ)
  have hEq : (fun q : ℝ => -scalarIntegrand (escapePoint+q)/3375) =ᶠ[nhdsWithin 0 (Ioi 0)]
      deriv (fun q : ℝ => scalarTotalFlux (escapePoint+q)) := by
    filter_upwards [hs.eventually (Ioo_mem_nhds escapePoint_mem.1 escapePoint_mem.2),
      self_mem_nhdsWithin] with q hI hq
    simp only [mem_Ioi] at hq
    have hne : escapePoint+q ≠ escapePoint := by linarith
    have hh := (scalarTotalFlux_hasDerivAt hI.1 hI.2
      (scalar_escape_factor_ne_zero hI.1 hne)).comp q
        ((hasDerivAt_const q escapePoint).add (hasDerivAt_id q))
    simpa only [Function.comp_def,id_eq,zero_add,mul_one] using hh.deriv.symm
  exact ht.congr' hEq

theorem scalarTotalFlux_escape_limit :
    ∃ L : ℝ, Tendsto scalarTotalFlux (nhdsWithin escapePoint {escapePoint}ᶜ) (nhds L) := by
  have hmono : nhdsWithin (0:ℝ) (Ioi 0) ≤ nhdsWithin 0 {0}ᶜ :=
    nhdsWithin_mono _ (fun q hq => by simp only [mem_compl_iff,mem_singleton_iff]; exact ne_of_gt hq)
  have hderiv := escapeRealNumerator_quotient_eventually.nhdsNE_deriv.filter_mono hmono
  have hlim : Tendsto (deriv (fun q : ℝ => escapeRealNumerator q/q^2))
      (nhdsWithin 0 (Ioi 0)) (nhds (-scalarIntegrand escapePoint/3375)) :=
    scalarTotalFlux_shift_derivative_limit.congr' hderiv.symm
  obtain ⟨G,hG,hEq⟩ := finitePoleTwo_removable escapeRealNumerator
    (-scalarIntegrand escapePoint/3375) escapeRealNumerator_analyticAt hlim
  have ht : Tendsto (fun q : ℝ => scalarTotalFlux (escapePoint+q))
      (nhdsWithin 0 {0}ᶜ) (nhds (G 0)) := by
    have he := escapeRealNumerator_quotient_eventually.symm.trans hEq
    exact (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm
  have hs : Tendsto (fun U : ℝ => U-escapePoint)
      (nhdsWithin escapePoint {escapePoint}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hi : Tendsto (fun U : ℝ => U) (nhdsWithin escapePoint {escapePoint}ᶜ)
          (nhds escapePoint) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [sub_self] using hi.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => escapePoint)
          (nhdsWithin escapePoint {escapePoint}ᶜ) (nhds escapePoint))
    · filter_upwards [self_mem_nhdsWithin] with U hU
      simp only [mem_compl_iff,mem_singleton_iff] at hU ⊢
      exact sub_ne_zero.mpr hU
  refine ⟨G 0,?_⟩
  have hh := ht.comp hs
  apply hh.congr'
  exact Filter.Eventually.of_forall (fun U => by
    simp only [Function.comp_apply]
    congr 1
    ring)

end Row12

#print axioms Row12.scalar_escape_factor_ne_zero
#print axioms Row12.escapeRealNumerator_analyticAt
#print axioms Row12.escapeRealNumerator_quotient_eventually
#print axioms Row12.scalarTotalFlux_shift_derivative_limit
#print axioms Row12.scalarTotalFlux_escape_limit
