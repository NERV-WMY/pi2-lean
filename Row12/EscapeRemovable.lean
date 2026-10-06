import Row12.AnalyticSecondUniqueness

open Set Filter
open scoped Topology

namespace Row12

theorem negativePole_derivative_leading (H : ℝ → ℝ) (m : ℕ) (q : ℝ)
    (hH : AnalyticAt ℝ H q) (hq : q ≠ 0) :
    q^(m+2)*deriv (fun z => H z/z^(m+1)) q =
      q*deriv H q-((m:ℝ)+1)*H q := by
  have hd := hH.differentiableAt.hasDerivAt.fun_div
    ((hasDerivAt_id q).fun_pow (m+1)) (pow_ne_zero _ hq)
  simp only [id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one] at hd
  rw [hd.deriv]
  simp only [pow_succ]
  field_simp [hq,pow_ne_zero m hq]

theorem negativePole_derivative_no_finite_limit (H : ℝ → ℝ) (m : ℕ) (L : ℝ)
    (hH : AnalyticAt ℝ H 0) (hH0 : H 0 ≠ 0) :
    ¬Tendsto (deriv (fun z => H z/z^(m+1))) (nhdsWithin 0 (Ioi 0)) (nhds L) := by
  intro hlim
  have hi : Tendsto (fun q : ℝ => q) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hleft : Tendsto (fun q : ℝ => q^(m+2)*deriv (fun z => H z/z^(m+1)) q)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [zero_pow (by omega : m+2 ≠ 0),zero_mul] using (hi.pow (m+2)).mul hlim
  have hright : Tendsto (fun q : ℝ => q*deriv H q-((m:ℝ)+1)*H q)
      (nhdsWithin 0 (Ioi 0)) (nhds (-((m:ℝ)+1)*H 0)) := by
    have hh : Tendsto H (nhdsWithin 0 (Ioi 0)) (nhds (H 0)) :=
      hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hdh : Tendsto (deriv H) (nhdsWithin 0 (Ioi 0)) (nhds (deriv H 0)) :=
      hH.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [zero_mul,zero_sub,neg_mul] using
      (hi.mul hdh).sub (tendsto_const_nhds.mul hh)
  have he : (fun q : ℝ => q^(m+2)*deriv (fun z => H z/z^(m+1)) q) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun q => q*deriv H q-((m:ℝ)+1)*H q) := by
    filter_upwards [hH.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with q hHq hq
    exact negativePole_derivative_leading H m q hHq (ne_of_gt hq)
  have hz : (0:ℝ) = -((m:ℝ)+1)*H 0 :=
    tendsto_nhds_unique (hleft.congr' he) hright
  have hm : -((m:ℝ)+1) ≠ 0 := by have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  exact (mul_ne_zero hm hH0) hz.symm

theorem finitePoleTwo_removable (g : ℝ → ℝ) (L : ℝ) (hg : AnalyticAt ℝ g 0)
    (hd : Tendsto (deriv (fun q => g q/q^2)) (nhdsWithin 0 (Ioi 0)) (nhds L)) :
    ∃ G : ℝ → ℝ, AnalyticAt ℝ G 0 ∧
      (fun q => g q/q^2) =ᶠ[nhdsWithin 0 {0}ᶜ] G := by
  by_cases hzero : g =ᶠ[nhds 0] 0
  · refine ⟨fun _ => 0,analyticAt_const,?_⟩
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds] with q hq
    simp only [hq,Pi.zero_apply,zero_div]
  obtain ⟨n,H,hH,hH0,hfactor⟩ := hg.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hzero
  have hf : g =ᶠ[nhds 0] (fun q => q^n*H q) := by
    change ∀ᶠ q in nhds 0, g q = q^n*H q
    simpa only [sub_zero,smul_eq_mul] using hfactor
  have hn : 2 ≤ n := by
    by_contra hn
    have hn2 : n < 2 := by omega
    interval_cases n
    · have he : (fun q => g q/q^2) =ᶠ[nhds 0] (fun q => H q/q^2) := by
        filter_upwards [hf] with q hq
        simp only [hq,pow_zero,one_mul]
      have ht := hd.congr' (he.deriv.filter_mono nhdsWithin_le_nhds)
      exact negativePole_derivative_no_finite_limit H 1 L hH hH0 ht
    · have he : (fun q => g q/q^2) =ᶠ[nhds 0] (fun q => H q/q) := by
        filter_upwards [hf] with q hq
        rw [hq]
        by_cases hq0 : q=0
        · simp [hq0]
        · simp only [pow_one]
          field_simp [hq0]
      have ht := hd.congr' (he.deriv.filter_mono nhdsWithin_le_nhds)
      exact negativePole_derivative_no_finite_limit H 0 L hH hH0 (by simpa only [zero_add,pow_one] using ht)
  refine ⟨fun q => q^(n-2)*H q,(analyticAt_id.pow (n-2)).mul hH,?_⟩
  filter_upwards [hf.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hq hq0
  have hne : q ≠ 0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hq0
  have hp : q^n=q^(n-2)*q^2 := by rw [← pow_add,Nat.sub_add_cancel hn]
  rw [hq,hp]
  field_simp [hne]

end Row12

#print axioms Row12.negativePole_derivative_leading
#print axioms Row12.negativePole_derivative_no_finite_limit
#print axioms Row12.finitePoleTwo_removable
