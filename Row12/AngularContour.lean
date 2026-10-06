import Row12.AngularNormalForm
import Row12.CircleParametric
import Row12.HadamardComplex

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

theorem nativeEuler_complex_analyticAt (k : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (nativeEuler k) q := by
  have hd : DifferentiableOn ℂ (nativeEuler k) (ball (0:ℂ) 1) := by
    intro z hz
    exact (nativeEuler_hasDerivAt k z (by simpa using hz)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa using hq))

theorem nativeState_entry_analyticAt (i : Fin 3) (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (fun z => nativeState z i) q := by
  fin_cases i <;> change AnalyticAt ℂ (nativeEuler _) q <;>
    exact nativeEuler_complex_analyticAt _ q hq

theorem angular_tensor_pair_continuousWithinAt
    {K : Set (ℂ × ℂ)} {p : ℂ × ℂ}
    (R : ℂ × ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (X Z : ℂ × ℂ → Fin 3 → ℂ)
    (hR : ∀ i j, ContinuousWithinAt (fun z => R z i j) K p)
    (hX : ∀ i, ContinuousWithinAt (fun z => X z i) K p)
    (hZ : ∀ i, ContinuousWithinAt (fun z => Z z i) K p) :
    ContinuousWithinAt (fun z => angularTensorPair (R z) (X z) (Z z)) K p := by
  unfold angularTensorPair
  exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
    ((hR i j).mul (hX i)).mul (hZ j)))

noncomputable def angularNFParameterValue (v : Fin 6 → ℂ) (lambda s : ℂ) : ℂ :=
  lambda⁻¹ * angularTensorPair
    (lambda • angularNFParameterDerivative v lambda s +
      angularNFRow v lambda s * nativeEulerConnection (lambda/s))
    (nativeState s) (nativeState (lambda/s))

theorem angular_nf_continuousOn (v : Fin 6 → ℂ) (K : Set (ℂ × ℂ))
    (hK : ∀ p ∈ K, p.2 ≠ 0 ∧ p.2 ≠ 1 ∧ p.2 ≠ p.1 ∧
      ‖p.2‖ < 1 ∧ ‖p.1/p.2‖ < 1) :
    ContinuousOn (fun p : ℂ × ℂ => angularNFIntegrand v p.1 p.2) K := by
  intro p hp
  obtain ⟨hs0,hs1,hsl,hs,hb⟩ := hK p hp
  have hdiv : ContinuousWithinAt (fun p : ℂ × ℂ => p.1/p.2) K p :=
    continuousWithinAt_fst.div continuousWithinAt_snd hs0
  have hX (i : Fin 3) : ContinuousWithinAt (fun p : ℂ × ℂ => nativeState p.2 i) K p :=
    (nativeState_entry_analyticAt i p.2 hs).continuousAt.comp_continuousWithinAt
      continuousWithinAt_snd
  have hZ (i : Fin 3) : ContinuousWithinAt (fun p : ℂ × ℂ => nativeState (p.1/p.2) i) K p :=
    ContinuousAt.comp_continuousWithinAt (f := fun p : ℂ × ℂ => p.1/p.2) (x := p)
      (nativeState_entry_analyticAt i (p.1/p.2) hb).continuousAt hdiv
  have hd1 : p.2-1 ≠ 0 := sub_ne_zero.mpr hs1
  have hdl : p.2-p.1 ≠ 0 := sub_ne_zero.mpr hsl
  apply angular_tensor_pair_continuousWithinAt (fun p => angularNFRow v p.1 p.2)
    (fun p => nativeState p.2) (fun p => nativeState (p.1/p.2)) _ hX hZ
  intro i j
  unfold angularNFRow
  fun_prop (disch := assumption)

theorem angular_nf_parameter_continuousOn (v : Fin 6 → ℂ) (K : Set (ℂ × ℂ))
    (hK : ∀ p ∈ K, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ≠ 1 ∧ p.2 ≠ p.1 ∧
      ‖p.2‖ < 1 ∧ ‖p.1/p.2‖ < 1) :
    ContinuousOn (fun p : ℂ × ℂ => angularNFParameterValue v p.1 p.2) K := by
  intro p hp
  obtain ⟨hl0,hs0,hs1,hsl,hs,hb⟩ := hK p hp
  have hdiv : ContinuousWithinAt (fun p : ℂ × ℂ => p.1/p.2) K p :=
    continuousWithinAt_fst.div continuousWithinAt_snd hs0
  have hX (i : Fin 3) : ContinuousWithinAt (fun p : ℂ × ℂ => nativeState p.2 i) K p :=
    (nativeState_entry_analyticAt i p.2 hs).continuousAt.comp_continuousWithinAt
      continuousWithinAt_snd
  have hZ (i : Fin 3) : ContinuousWithinAt (fun p : ℂ × ℂ => nativeState (p.1/p.2) i) K p :=
    ContinuousAt.comp_continuousWithinAt (f := fun p : ℂ × ℂ => p.1/p.2) (x := p)
      (nativeState_entry_analyticAt i (p.1/p.2) hb).continuousAt hdiv
  have hd1 : p.2-1 ≠ 0 := sub_ne_zero.mpr hs1
  have hdl : p.2-p.1 ≠ 0 := sub_ne_zero.mpr hsl
  have hdl2 : (p.2-p.1)^2 ≠ 0 := pow_ne_zero 2 hdl
  have hb1 : p.1/p.2 ≠ 1 := by intro he; simp [he] at hb
  have hdb : 1-p.1/p.2 ≠ 0 := sub_ne_zero.mpr hb1.symm
  have hD1 : ContinuousWithinAt (fun p : ℂ × ℂ => p.2-1) K p :=
    continuousWithinAt_snd.sub continuousWithinAt_const
  have hDl : ContinuousWithinAt (fun p : ℂ × ℂ => p.2-p.1) K p :=
    continuousWithinAt_snd.sub continuousWithinAt_fst
  have hR (i j : Fin 3) : ContinuousWithinAt (fun p : ℂ × ℂ => angularNFRow v p.1 p.2 i j) K p :=
    (continuousWithinAt_const.div hD1 hd1).add (continuousWithinAt_const.div hDl hdl)
  have hR' (i j : Fin 3) : ContinuousWithinAt
      (fun p : ℂ × ℂ => angularNFParameterDerivative v p.1 p.2 i j) K p :=
    continuousWithinAt_const.div (hDl.pow 2) hdl2
  have hquot (c d : ℂ) (hd : d ≠ 0) : ContinuousWithinAt
      (fun p : ℂ × ℂ => c*(p.1/p.2)/(d*(1-p.1/p.2))) K p :=
    (continuousWithinAt_const.mul hdiv).div
      (continuousWithinAt_const.mul (continuousWithinAt_const.sub hdiv)) (mul_ne_zero hd hdb)
  have hN (i j : Fin 3) : ContinuousWithinAt
      (fun p : ℂ × ℂ => nativeEulerConnection (p.1/p.2) i j) K p := by
    fin_cases i <;> fin_cases j
    · exact continuousWithinAt_const
    · exact continuousWithinAt_const
    · exact continuousWithinAt_const
    · exact continuousWithinAt_const
    · exact continuousWithinAt_const
    · exact continuousWithinAt_const
    · exact hquot 5 72 (by norm_num)
    · exact hquot 23 36 (by norm_num)
    · exact hquot 3 2 (by norm_num)
  unfold angularNFParameterValue
  apply (continuousWithinAt_fst.inv₀ hl0).mul
  apply angular_tensor_pair_continuousWithinAt
    (fun p => p.1 • angularNFParameterDerivative v p.1 p.2 +
      angularNFRow v p.1 p.2 * nativeEulerConnection (p.1/p.2))
    (fun p => nativeState p.2) (fun p => nativeState (p.1/p.2)) _ hX hZ
  intro i j
  change ContinuousWithinAt (fun p : ℂ × ℂ => p.1*angularNFParameterDerivative v p.1 p.2 i j +
    ∑ k : Fin 3, angularNFRow v p.1 p.2 i k*nativeEulerConnection (p.1/p.2) k j) K p
  exact (continuousWithinAt_fst.mul (hR' i j)).add
    (tendsto_finsetSum _ (fun k _ => (hR i k).mul (hN k j)))

noncomputable def angularNFIntegral (v : Fin 6 → ℂ) (lambda : ℂ) (r : ℝ) : ℂ :=
  (2*Real.pi*I : ℂ)⁻¹ * ∮ s in C(0,r), angularNFIntegrand v lambda s

noncomputable def angularContourState (lambda : ℂ) (r : ℝ) : Fin 6 → ℂ :=
  fun i => angularNFIntegral (Pi.single i 1) lambda r

theorem angular_circle_domain {lambda s : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖lambda‖ < r) (hs : s ∈ sphere 0 r) :
    s ≠ 0 ∧ s ≠ 1 ∧ s ≠ lambda ∧ ‖s‖ < 1 ∧ ‖lambda/s‖ < 1 := by
  have hsr : ‖s‖ = r := by simpa using mem_sphere.mp hs
  have hs0 : s ≠ 0 := norm_ne_zero_iff.mp (hsr.symm ▸ hr.ne')
  have hsn : ‖s‖ < 1 := hsr ▸ hr1
  have hs1 : s ≠ 1 := by intro he; simp [he] at hsn
  have hsl : s ≠ lambda := by intro he; rw [he] at hsr; linarith
  refine ⟨hs0,hs1,hsl,hsn,?_⟩
  rw [norm_div, hsr]
  exact (div_lt_one hr).2 hl

theorem angular_nf_circleIntegrable (v : Fin 6 → ℂ) (lambda : ℂ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖lambda‖ < r) :
    CircleIntegrable (angularNFIntegrand v lambda) 0 r := by
  have hY (i : Fin 3) : ContinuousOn (fun s : ℂ => nativeState s i) (sphere 0 r) := by
    intro s hs
    exact (nativeState_entry_analyticAt i s (angular_circle_domain hr hr1 hl hs).2.2.2.1).continuousAt.continuousWithinAt
  have hYb (i : Fin 3) : ContinuousOn (fun s : ℂ => nativeState (lambda/s) i) (sphere 0 r) := by
    intro s hs
    have hd := angular_circle_domain hr hr1 hl hs
    exact ContinuousAt.comp_continuousWithinAt (f := fun s : ℂ => lambda/s) (x := s)
      (nativeState_entry_analyticAt i (lambda/s) hd.2.2.2.2).continuousAt
      (continuousWithinAt_const.div continuousWithinAt_id hd.1)
  have hDot (w : Fin 3 → ℂ) : ContinuousOn (fun s : ℂ => dotProduct w (nativeState s)) (sphere 0 r) := by
    exact continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (hY i))
  have hDotb (w : Fin 3 → ℂ) : ContinuousOn (fun s : ℂ => dotProduct w (nativeState (lambda/s))) (sphere 0 r) := by
    exact continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (hYb i))
  have hsub1 : ∀ s ∈ sphere (0:ℂ) r, s-1 ≠ 0 :=
    fun s hs => sub_ne_zero.mpr (angular_circle_domain hr hr1 hl hs).2.1
  have hsubl : ∀ s ∈ sphere (0:ℂ) r, s-lambda ≠ 0 :=
    fun s hs => sub_ne_zero.mpr (angular_circle_domain hr hr1 hl hs).2.2.1
  have hc : ContinuousOn (angularNFIntegrand v lambda) (sphere 0 r) := by
    change ContinuousOn (fun s => angularNFIntegrand v lambda s) (sphere 0 r)
    simp_rw [angular_nf_integrand_formula]
    exact ((hDot angularNFWeight).mul (hDotb (angularNFFirst v))).div
      (continuousOn_id.sub continuousOn_const) hsub1 |>.add
      (((hDot (angularNFSecond v)).mul (hDotb angularNFWeight)).div
        (continuousOn_id.sub continuousOn_const) hsubl)
  exact hc.circleIntegrable hr.le

theorem angular_nf_integral_anchor (lambda : ℂ) {r : ℝ}
    (hl0 : lambda ≠ 0) (hr : 0 < r) (hr1 : r < 1) (hl : ‖lambda‖ < r) :
    angularNFIntegral (sixthCyclicMatrix 0) lambda r = squaredNativeEuler 0 lambda := by
  have hp (s : ℂ) (hs : s ∈ sphere 0 r) :
      HasDerivAt (angularAnchorPrimitive lambda)
        (deriv (angularAnchorPrimitive lambda) s) s := by
    obtain ⟨hs0,_,_,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
    exact (angular_anchor_primitive_hasDerivAt lambda s hl0 hs0 hsn hbn).differentiableAt.hasDerivAt
  have hPzero := circleIntegral_exactDerivative (angularAnchorPrimitive lambda)
    (deriv (angularAnchorPrimitive lambda)) hr.le hp
  have hFi := angular_nf_circleIntegrable (sixthCyclicMatrix 0) lambda hr hr1 hl
  have hnative : CircleIntegrable (fun s => nativeF s*nativeF (lambda/s)/s) 0 r := by
    have hc : ContinuousOn (fun s => nativeF s*nativeF (lambda/s)/s) (sphere 0 r) := by
      intro s hs
      obtain ⟨hs0,_,_,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
      exact (((nativeF_analyticAt s hsn).continuousAt.continuousWithinAt).mul
        ((nativeF_analyticAt (lambda/s) hbn).continuousAt.comp_continuousWithinAt
          (continuousWithinAt_const.div continuousWithinAt_id hs0))).div
            continuousWithinAt_id hs0
    exact hc.circleIntegrable hr.le
  have heq (s : ℂ) (hs : s ∈ sphere 0 r) :
      deriv (angularAnchorPrimitive lambda) s =
        nativeF s*nativeF (lambda/s)/s-angularNFIntegrand (sixthCyclicMatrix 0) lambda s := by
    obtain ⟨hs0,hs1,hsl,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
    linear_combination -angular_nf_actual_anchor lambda s hl0 hs0 hs1 hsl hsn hbn
  have hPi : CircleIntegrable (deriv (angularAnchorPrimitive lambda)) 0 r := by
    apply (circleIntegrable_congr (by
      intro s hs
      exact heq s (by simpa only [abs_of_nonneg hr.le] using hs))).2
    exact hnative.sub hFi
  have hi : (∮ s in C(0,r), nativeF s*nativeF (lambda/s)/s) =
      (∮ s in C(0,r), angularNFIntegrand (sixthCyclicMatrix 0) lambda s) := by
    calc
      _ = ∮ s in C(0,r), angularNFIntegrand (sixthCyclicMatrix 0) lambda s +
          deriv (angularAnchorPrimitive lambda) s := by
        apply circleIntegral.integral_congr hr.le
        intro s hs
        obtain ⟨hs0,hs1,hsl,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
        exact angular_nf_actual_anchor lambda s hl0 hs0 hs1 hsl hsn hbn
      _ = _ := by rw [circleIntegral.integral_add hFi hPi, hPzero, add_zero]
  have hs := hadamardComplexEuler_hasSum 0 lambda hr hl hr1
  have hsq := (squaredNativeEuler_summable 0 lambda (hl.trans hr1)).hasSum
  have hh : hadamardComplexEulerIntegral 0 lambda r = squaredNativeEuler 0 lambda := by
    apply hs.unique
    simpa only [squaredNativeEuler, RCLike.ofReal_eq_complex_ofReal, pow_zero,
      mul_one] using hsq
  change (2*Real.pi*I : ℂ)⁻¹ *
    (∮ s in C(0,r), nativeF s*nativeF (lambda/s)/s) = _ at hh
  rw [hi] at hh
  exact hh

theorem angular_parameter_closedBall {lambda : ℂ} {r : ℝ}
    (hl0 : lambda ≠ 0) (hl : ‖lambda‖ < r) :
    ∃ ε > 0, ∀ z ∈ closedBall lambda ε, z ≠ 0 ∧ ‖z‖ < r := by
  have hne : ∀ᶠ z in nhds lambda, z ≠ (0:ℂ) := eventually_ne_nhds hl0
  have hn : ∀ᶠ z in nhds lambda, ‖z‖ < r :=
    continuous_norm.continuousAt.tendsto.eventually (Iio_mem_nhds hl)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hne.and hn)
  refine ⟨δ/2,by positivity,?_⟩
  intro z hz
  apply hball
  exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (by linarith))

set_option maxHeartbeats 1200000 in
theorem angular_nf_integral_hasDerivAt (v : Fin 6 → ℂ) (lambda : ℂ) {r : ℝ}
    (hl0 : lambda ≠ 0) (hr : 0 < r) (hr1 : r < 1) (hl : ‖lambda‖ < r) :
    HasDerivAt (fun z => angularNFIntegral v z r)
      (lambda⁻¹*angularNFIntegral (Matrix.vecMul v (sixthB6 lambda)) lambda r) lambda := by
  obtain ⟨ε,hε,hεall⟩ := angular_parameter_closedBall hl0 hl
  let K : Set (ℂ × ℂ) := closedBall lambda ε ×ˢ sphere (0:ℂ) r
  have hDom (p : ℂ × ℂ) (hp : p ∈ K) :
      p.2 ≠ 0 ∧ p.2 ≠ 1 ∧ p.2 ≠ p.1 ∧ ‖p.2‖ < 1 ∧ ‖p.1/p.2‖ < 1 :=
    angular_circle_domain hr hr1 (hεall p.1 hp.1).2 hp.2
  have hDom' (p : ℂ × ℂ) (hp : p ∈ K) : p.1 ≠ 0 ∧
      p.2 ≠ 0 ∧ p.2 ≠ 1 ∧ p.2 ≠ p.1 ∧ ‖p.2‖ < 1 ∧ ‖p.1/p.2‖ < 1 :=
    ⟨(hεall p.1 hp.1).1,hDom p hp⟩
  have hF := angular_nf_continuousOn v K hDom
  have hF' := angular_nf_parameter_continuousOn v K hDom'
  have hraw := circleParametric_hasDerivAt
    (fun z s => angularNFIntegrand v z s) (fun z s => angularNFParameterValue v z s)
    lambda 0 r ε hr.le hε hF hF' (by
      intro z hz s hs
      obtain ⟨hs0,_,hsl,_,hb⟩ := angular_circle_domain hr hr1 (hεall z hz).2 hs
      exact angular_nf_integrand_parameter_hasDerivAt v z s (hεall z hz).1 hs0 hsl hb)
  have hl1 : lambda ≠ 1 := by intro he; simp [he] at hl; linarith
  have hid (s : ℂ) (hs : s ∈ sphere 0 r) :
      lambda*angularNFParameterValue v lambda s =
        angularNFIntegrand (Matrix.vecMul v (sixthB6 lambda)) lambda s +
          deriv (angularNFPrimitive v lambda) s := by
    obtain ⟨hs0,hs1,hsl,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
    have hh := angular_nf_actual_euler_action v lambda s hl0 hl1 hs0 hs1 hsl hsn hbn
    rw [(angular_nf_integrand_parameter_hasDerivAt v lambda s hl0 hs0 hsl hbn).deriv] at hh
    exact hh
  have hP (s : ℂ) (hs : s ∈ sphere 0 r) :
      HasDerivAt (angularNFPrimitive v lambda) (deriv (angularNFPrimitive v lambda) s) s := by
    obtain ⟨hs0,_,hsl,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
    exact (angular_nf_primitive_hasDerivAt v lambda s hl0 hs0 hsl hsn hbn).differentiableAt.hasDerivAt
  have hPzero := circleIntegral_exactDerivative (angularNFPrimitive v lambda)
    (deriv (angularNFPrimitive v lambda)) hr.le hP
  have hac : lambda ∈ closedBall lambda ε := mem_closedBall_self hε.le
  have hDi : CircleIntegrable (angularNFParameterValue v lambda) 0 r := by
    have hm : MapsTo (fun s : ℂ => (lambda,s)) (sphere 0 r) K :=
      fun s hs => ⟨hac,hs⟩
    have hc : ContinuousOn (fun s : ℂ => (lambda,s)) (sphere 0 r) :=
      continuousOn_const.prodMk continuousOn_id
    have hh : ContinuousOn (angularNFParameterValue v lambda) (sphere 0 r) :=
      hF'.comp hc hm
    exact hh.circleIntegrable hr.le
  have hNi := angular_nf_circleIntegrable (Matrix.vecMul v (sixthB6 lambda)) lambda hr hr1 hl
  have hPi : CircleIntegrable (deriv (angularNFPrimitive v lambda)) 0 r := by
    apply (circleIntegrable_congr (by
      intro s hs
      have hh := hid s (by simpa only [abs_of_nonneg hr.le] using hs)
      have he : deriv (angularNFPrimitive v lambda) s =
          lambda*angularNFParameterValue v lambda s-
            angularNFIntegrand (Matrix.vecMul v (sixthB6 lambda)) lambda s := by
        linear_combination -hh
      exact he)).2
    exact (hDi.const_mul lambda).sub hNi
  have hi : lambda*(∮ s in C(0,r), angularNFParameterValue v lambda s) =
      ∮ s in C(0,r), angularNFIntegrand (Matrix.vecMul v (sixthB6 lambda)) lambda s := by
    rw [← circleIntegral.integral_const_mul]
    calc
      _ = ∮ s in C(0,r), angularNFIntegrand (Matrix.vecMul v (sixthB6 lambda)) lambda s +
          deriv (angularNFPrimitive v lambda) s :=
        circleIntegral.integral_congr hr.le hid
      _ = _ := by rw [circleIntegral.integral_add hNi hPi,hPzero,add_zero]
  have hh := hraw.const_mul (2*Real.pi*I : ℂ)⁻¹
  apply hh.congr_deriv
  change (2*Real.pi*I : ℂ)⁻¹*(∮ s in C(0,r), angularNFParameterValue v lambda s) = _
  calc
    _ = lambda⁻¹*((2*Real.pi*I : ℂ)⁻¹*
        (lambda*(∮ s in C(0,r), angularNFParameterValue v lambda s))) := by
      field_simp [hl0]
    _ = _ := by rw [hi]; rfl

end Row12

#print axioms Row12.nativeState_entry_analyticAt
#print axioms Row12.nativeEuler_complex_analyticAt
#print axioms Row12.angular_tensor_pair_continuousWithinAt
#print axioms Row12.angular_nf_continuousOn
#print axioms Row12.angular_nf_parameter_continuousOn
#print axioms Row12.angular_circle_domain
#print axioms Row12.angular_nf_circleIntegrable
#print axioms Row12.angular_nf_integral_anchor
#print axioms Row12.angular_parameter_closedBall
#print axioms Row12.angular_nf_integral_hasDerivAt
