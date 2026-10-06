import Row12.HalfGaussSeries
import Row12.GaussQuadratic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness

open Set Filter
open scoped Topology

namespace Row12

noncomputable def realNativeSecond (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  144*(1-q)*nativeTheta (nativeTheta f) q-72*q*nativeTheta f q-5*q*f q

theorem nativeTheta_eventually_congr {f g : ℝ → ℝ} {q : ℝ}
    (he : f =ᶠ[nhds q] g) : nativeTheta f =ᶠ[nhds q] nativeTheta g := by
  filter_upwards [he.deriv] with z hz
  simp only [nativeTheta, hz]

theorem realNativeSecond_eventually_congr {f g : ℝ → ℝ} {q : ℝ}
    (he : f =ᶠ[nhds q] g) : realNativeSecond f =ᶠ[nhds q] realNativeSecond g := by
  have ht := nativeTheta_eventually_congr he
  have htt := nativeTheta_eventually_congr ht
  filter_upwards [he, ht, htt] with z hz htz httz
  simp only [realNativeSecond, hz, htz, httz]

theorem nativeTheta_pow_mul (n : ℕ) (H : ℝ → ℝ) (q : ℝ)
    (hH : DifferentiableAt ℝ H q) :
    nativeTheta (fun z => z^n*H z) q = q^n*((n:ℝ)*H q+q*deriv H q) := by
  have hd := ((hasDerivAt_id q).fun_pow n).fun_mul hH.hasDerivAt
  simp only [id_eq, mul_one] at hd
  rw [nativeTheta, hd.deriv]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem nativeTheta_second_pow_mul (n : ℕ) (H : ℝ → ℝ) (q : ℝ)
    (hH : AnalyticAt ℝ H q) :
    nativeTheta (nativeTheta (fun z => z^n*H z)) q =
      q^n*((n:ℝ)^2*H q+(2*(n:ℝ)+1)*q*deriv H q+q^2*deriv (deriv H) q) := by
  let H1 : ℝ → ℝ := fun z => (n:ℝ)*H z+z*deriv H z
  have he : nativeTheta (fun z => z^n*H z) =ᶠ[nhds q] (fun z => z^n*H1 z) := by
    filter_upwards [hH.eventually_analyticAt] with z hz
    exact nativeTheta_pow_mul n H z hz.differentiableAt
  have hH1 : HasDerivAt H1 ((n:ℝ)*deriv H q+deriv H q+q*deriv (deriv H) q) q := by
    have hd := (hH.differentiableAt.hasDerivAt.const_mul (n:ℝ)).add
      ((hasDerivAt_id q).mul hH.deriv.differentiableAt.hasDerivAt)
    apply hd.congr_deriv
    simp only [id_eq, one_mul]
    ring
  rw [nativeTheta, he.deriv_eq]
  change nativeTheta (fun z => z^n*H1 z) q = _
  rw [nativeTheta_pow_mul n H1 q hH1.differentiableAt, hH1.deriv]
  dsimp only [H1]
  ring

noncomputable def secondLeadingFactor (n : ℕ) (H : ℝ → ℝ) (q : ℝ) : ℝ :=
  144*(1-q)*((n:ℝ)^2*H q+(2*(n:ℝ)+1)*q*deriv H q+q^2*deriv (deriv H) q)-
    72*q*((n:ℝ)*H q+q*deriv H q)-5*q*H q

theorem realNativeSecond_pow_mul (n : ℕ) (H : ℝ → ℝ) (q : ℝ)
    (hH : AnalyticAt ℝ H q) :
    realNativeSecond (fun z => z^n*H z) q = q^n*secondLeadingFactor n H q := by
  rw [realNativeSecond, nativeTheta_second_pow_mul n H q hH,
    nativeTheta_pow_mul n H q hH.differentiableAt]
  dsimp only [secondLeadingFactor]
  ring

theorem analytic_nativeSecond_zero {f : ℝ → ℝ} (ha : AnalyticAt ℝ f 0)
    (h0 : f 0 = 0) (he : realNativeSecond f =ᶠ[nhds 0] 0) :
    f =ᶠ[nhds 0] 0 := by
  by_contra hnot
  obtain ⟨n, H, hHa, hH0, hfH⟩ := ha.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnot
  have hfH' : f =ᶠ[nhds 0] (fun q => q^n*H q) := by
    change ∀ᶠ q in nhds 0, f q = q^n*H q
    simpa only [sub_zero, smul_eq_mul] using hfH
  have hn : n ≠ 0 := by
    intro hn
    have h := hfH'.self_of_nhds
    simp only [h0, hn, pow_zero, one_mul] at h
    exact hH0 h.symm
  have hsecond : realNativeSecond (fun q => q^n*H q) =ᶠ[nhds 0] 0 :=
    (realNativeSecond_eventually_congr hfH').symm.trans he
  have hzero : secondLeadingFactor n H =ᶠ[nhdsWithin 0 (Ioi 0)] 0 := by
    filter_upwards [hsecond.filter_mono nhdsWithin_le_nhds,
      hHa.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with q hq hHq hqpos
    have hqne : q ≠ 0 := ne_of_gt hqpos
    rw [realNativeSecond_pow_mul n H q hHq] at hq
    exact (mul_eq_zero.mp hq).resolve_left (pow_ne_zero n hqne)
  have hc : ContinuousAt (secondLeadingFactor n H) 0 := by
    have hHc := hHa.continuousAt
    have hHdc := hHa.deriv.continuousAt
    have hHddc := hHa.deriv.deriv.continuousAt
    unfold secondLeadingFactor
    fun_prop
  have hz : secondLeadingFactor n H 0 = 0 :=
    tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hzero.symm)
  have hnreal : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hproduct : (144:ℝ)*(n:ℝ)^2*H 0 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hnreal)) hH0
  apply hproduct
  simpa [secondLeadingFactor, mul_assoc] using hz

theorem realNativeSecond_eventually_sub {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    realNativeSecond (fun q => f q-g q) =ᶠ[nhds 0]
      (fun q => realNativeSecond f q-realNativeSecond g q) := by
  have hd : deriv (fun q => f q-g q) =ᶠ[nhds 0] (fun q => deriv f q-deriv g q) := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with q hfq hgq
    exact (hfq.differentiableAt.hasDerivAt.sub hgq.differentiableAt.hasDerivAt).deriv
  have ht : nativeTheta (fun q => f q-g q) =ᶠ[nhds 0]
      (fun q => nativeTheta f q-nativeTheta g q) := by
    filter_upwards [hd] with q hq
    simp only [nativeTheta, hq, mul_sub]
  have htf : AnalyticAt ℝ (nativeTheta f) 0 := analyticAt_id.mul hf.deriv
  have htg : AnalyticAt ℝ (nativeTheta g) 0 := analyticAt_id.mul hg.deriv
  have htt : nativeTheta (nativeTheta (fun q => f q-g q)) =ᶠ[nhds 0]
      (fun q => nativeTheta (nativeTheta f) q-nativeTheta (nativeTheta g) q) := by
    have hh := nativeTheta_eventually_congr ht
    filter_upwards [hh, htf.eventually_analyticAt, htg.eventually_analyticAt] with q hq hfq hgq
    rw [hq, nativeTheta,
      (hfq.differentiableAt.hasDerivAt.fun_sub hgq.differentiableAt.hasDerivAt).deriv]
    simp only [nativeTheta, mul_sub]
  filter_upwards [ht, htt] with q hq hqq
  simp only [realNativeSecond, hq, hqq]
  ring

theorem normalized_nativeSecond_eq_eventually {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (h0 : f 0 = g 0)
    (heF : realNativeSecond f =ᶠ[nhds 0] 0)
    (heG : realNativeSecond g =ᶠ[nhds 0] 0) : f =ᶠ[nhds 0] g := by
  have he : realNativeSecond (fun q => f q-g q) =ᶠ[nhds 0] 0 := by
    filter_upwards [realNativeSecond_eventually_sub hf hg, heF, heG] with q hq hFq hGq
    simp only [hq, hFq, hGq, Pi.zero_apply, sub_self]
  have hz := analytic_nativeSecond_zero (hf.sub hg) (sub_eq_zero.mpr h0) he
  filter_upwards [hz] with q hq
  exact sub_eq_zero.mp hq

theorem nativeTheta_second_eq {f : ℝ → ℝ} {q : ℝ} (hf : AnalyticAt ℝ f q) :
    nativeTheta (nativeTheta f) q = q*deriv f q+q^2*deriv (deriv f) q := by
  have hd := (hasDerivAt_id q).fun_mul hf.deriv.differentiableAt.hasDerivAt
  simp only [id_eq, one_mul] at hd
  change q*deriv (fun z => z*deriv f z) q = _
  rw [hd.deriv]
  ring

theorem halfGauss_nativeSecond (q : ℝ) (hq : ‖q‖ < 1) :
    realNativeSecond halfGauss q = 0 := by
  rw [realNativeSecond, nativeTheta_second_eq (halfGauss_analyticAt q hq)]
  dsimp only [nativeTheta]
  linear_combination (144*q)*halfGauss_equation q hq

theorem gaussG_eq_halfGauss_eventually : (gaussG : ℝ → ℝ) =ᶠ[nhds 0] halfGauss := by
  apply normalized_nativeSecond_eq_eventually
    (gaussG_analyticAt 0 (by norm_num) (by norm_num))
    (halfGauss_analyticAt 0 (by norm_num))
  · rw [gaussG_zero, halfGauss_zero]
  · have hb : Ioo (-1:ℝ) 1 ∈ nhds (0:ℝ) := isOpen_Ioo.mem_nhds (by norm_num)
    filter_upwards [hb] with q hq
    exact gaussG_nativeSecond q (by linarith [hq.1]) hq.2
  · have hb : Ioo (-1:ℝ) 1 ∈ nhds (0:ℝ) := isOpen_Ioo.mem_nhds (by norm_num)
    filter_upwards [hb] with q hq
    exact halfGauss_nativeSecond q (by simpa only [Real.norm_eq_abs, abs_lt, mem_Ioo] using hq)

theorem gaussG_eq_halfGauss (q : ℝ) (hq : ‖q‖ < 1) : gaussG q = halfGauss q := by
  have hf : AnalyticOnNhd ℝ gaussG (Ioo (-1:ℝ) 1) := by
    intro z hz
    exact gaussG_analyticAt z (by linarith [hz.1]) hz.2
  have hg : AnalyticOnNhd ℝ (halfGauss : ℝ → ℝ) (Ioo (-1:ℝ) 1) := by
    intro z hz
    exact halfGauss_analyticAt z (by simpa only [Real.norm_eq_abs, abs_lt, mem_Ioo] using hz)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_Ioo
    (by norm_num : (0:ℝ) ∈ Ioo (-1:ℝ) 1) gaussG_eq_halfGauss_eventually
    (by simpa only [Real.norm_eq_abs, abs_lt, mem_Ioo] using hq)

theorem nativeF_eq_gaussG_square (q : ℝ) (hq : ‖q‖ < 1) : nativeF q = gaussG q^2 := by
  rw [nativeF_eq_halfGauss_square q hq, gaussG_eq_halfGauss q hq]

noncomputable def regularSecond (a b c f : ℝ → ℝ) (q : ℝ) : ℝ :=
  a q*nativeTheta (nativeTheta f) q+b q*nativeTheta f q+c q*f q

theorem regularSecond_eventually_congr (a b c : ℝ → ℝ) {f g : ℝ → ℝ}
    (he : f =ᶠ[nhds 0] g) : regularSecond a b c f =ᶠ[nhds 0] regularSecond a b c g := by
  have ht := nativeTheta_eventually_congr he
  have htt := nativeTheta_eventually_congr ht
  filter_upwards [he, ht, htt] with q hq htq httq
  simp only [regularSecond, hq, htq, httq]

noncomputable def regularLeadingFactor (a b c : ℝ → ℝ) (n : ℕ) (H : ℝ → ℝ) (q : ℝ) : ℝ :=
  a q*((n:ℝ)^2*H q+(2*(n:ℝ)+1)*q*deriv H q+q^2*deriv (deriv H) q)+
    b q*((n:ℝ)*H q+q*deriv H q)+c q*H q

theorem regularSecond_pow_mul (a b c : ℝ → ℝ) (n : ℕ) (H : ℝ → ℝ) (q : ℝ)
    (hH : AnalyticAt ℝ H q) :
    regularSecond a b c (fun z => z^n*H z) q = q^n*regularLeadingFactor a b c n H q := by
  rw [regularSecond, nativeTheta_second_pow_mul n H q hH,
    nativeTheta_pow_mul n H q hH.differentiableAt]
  dsimp only [regularLeadingFactor]
  ring

theorem analytic_regularSecond_zero (a b c : ℝ → ℝ)
    (ha : ContinuousAt a 0) (hb : ContinuousAt b 0) (hc : ContinuousAt c 0)
    (ha0 : a 0 ≠ 0) (hb0 : b 0 = 0) (hc0 : c 0 = 0)
    {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (hf0 : f 0 = 0)
    (he : regularSecond a b c f =ᶠ[nhdsWithin 0 (Ioi 0)] 0) :
    f =ᶠ[nhds 0] 0 := by
  by_contra hnot
  obtain ⟨n,H,hHa,hH0,hfH⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnot
  have hfH' : f =ᶠ[nhds 0] (fun q => q^n*H q) := by
    change ∀ᶠ q in nhds 0, f q = q^n*H q
    simpa only [sub_zero, smul_eq_mul] using hfH
  have hn : n ≠ 0 := by
    intro hn
    have h := hfH'.self_of_nhds
    simp only [hf0, hn, pow_zero, one_mul] at h
    exact hH0 h.symm
  have hsecond : regularSecond a b c (fun q => q^n*H q) =ᶠ[nhdsWithin 0 (Ioi 0)] 0 :=
    ((regularSecond_eventually_congr a b c hfH').symm.filter_mono nhdsWithin_le_nhds).trans he
  have hzero : regularLeadingFactor a b c n H =ᶠ[nhdsWithin 0 (Ioi 0)] 0 := by
    filter_upwards [hsecond, hHa.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with q hq hHq hqpos
    rw [regularSecond_pow_mul a b c n H q hHq] at hq
    exact (mul_eq_zero.mp hq).resolve_left (pow_ne_zero n (ne_of_gt hqpos))
  have hcontinuous : ContinuousAt (regularLeadingFactor a b c n H) 0 := by
    have hHc := hHa.continuousAt
    have hHdc := hHa.deriv.continuousAt
    have hHddc := hHa.deriv.deriv.continuousAt
    unfold regularLeadingFactor
    fun_prop
  have hz : regularLeadingFactor a b c n H 0 = 0 :=
    tendsto_nhds_unique (hcontinuous.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hzero.symm)
  have hnreal : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hproduct : a 0*(n:ℝ)^2*H 0 ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha0 (pow_ne_zero 2 hnreal)) hH0
  apply hproduct
  simpa [regularLeadingFactor, hb0, hc0, mul_assoc] using hz

theorem nativeTheta_eventually_sub {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    nativeTheta (fun q => f q-g q) =ᶠ[nhds 0]
      (fun q => nativeTheta f q-nativeTheta g q) := by
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with q hfq hgq
  rw [nativeTheta, (hfq.differentiableAt.hasDerivAt.fun_sub hgq.differentiableAt.hasDerivAt).deriv]
  simp only [nativeTheta, mul_sub]

theorem regularSecond_eventually_sub (a b c : ℝ → ℝ) {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    regularSecond a b c (fun q => f q-g q) =ᶠ[nhds 0]
      (fun q => regularSecond a b c f q-regularSecond a b c g q) := by
  have ht := nativeTheta_eventually_sub hf hg
  have htf : AnalyticAt ℝ (nativeTheta f) 0 := analyticAt_id.mul hf.deriv
  have htg : AnalyticAt ℝ (nativeTheta g) 0 := analyticAt_id.mul hg.deriv
  have htt := (nativeTheta_eventually_congr ht).trans (nativeTheta_eventually_sub htf htg)
  filter_upwards [ht, htt] with q hq hqq
  simp only [regularSecond, hq, hqq]
  ring

theorem normalized_regularSecond_eq_eventually (a b c : ℝ → ℝ)
    (ha : ContinuousAt a 0) (hb : ContinuousAt b 0) (hc : ContinuousAt c 0)
    (ha0 : a 0 ≠ 0) (hb0 : b 0 = 0) (hc0 : c 0 = 0) {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (h0 : f 0 = g 0)
    (heF : regularSecond a b c f =ᶠ[nhdsWithin 0 (Ioi 0)] 0)
    (heG : regularSecond a b c g =ᶠ[nhdsWithin 0 (Ioi 0)] 0) : f =ᶠ[nhds 0] g := by
  have he : regularSecond a b c (fun q => f q-g q) =ᶠ[nhdsWithin 0 (Ioi 0)] 0 := by
    filter_upwards [(regularSecond_eventually_sub a b c hf hg).filter_mono nhdsWithin_le_nhds,
      heF, heG] with q hq hFq hGq
    simp only [hq, hFq, hGq, Pi.zero_apply, sub_self]
  have hz := analytic_regularSecond_zero a b c ha hb hc ha0 hb0 hc0
    (hf.sub hg) (sub_eq_zero.mpr h0) he
  filter_upwards [hz] with q hq
  exact sub_eq_zero.mp hq

end Row12

#print axioms Row12.nativeTheta_eventually_congr
#print axioms Row12.realNativeSecond_eventually_congr
#print axioms Row12.nativeTheta_pow_mul
#print axioms Row12.nativeTheta_second_pow_mul
#print axioms Row12.realNativeSecond_pow_mul
#print axioms Row12.analytic_nativeSecond_zero
#print axioms Row12.realNativeSecond_eventually_sub
#print axioms Row12.normalized_nativeSecond_eq_eventually
#print axioms Row12.nativeTheta_second_eq
#print axioms Row12.halfGauss_nativeSecond
#print axioms Row12.gaussG_eq_halfGauss_eventually
#print axioms Row12.gaussG_eq_halfGauss
#print axioms Row12.nativeF_eq_gaussG_square
#print axioms Row12.regularSecond_eventually_congr
#print axioms Row12.regularSecond_pow_mul
#print axioms Row12.analytic_regularSecond_zero
#print axioms Row12.nativeTheta_eventually_sub
#print axioms Row12.regularSecond_eventually_sub
#print axioms Row12.normalized_regularSecond_eq_eventually
