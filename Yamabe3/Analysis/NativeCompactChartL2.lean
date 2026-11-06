import Yamabe3.Analysis.NativeCoordinateExtensionEnergy
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual compact chart transport on native L2 classes

The retained-volume L2 map is built from the explicit zero-extended
coordinate function, with a fixed compact-set indicator. Its bound is
derived from the actual density. Integrability uses the proved chart
measure identity, and AE congruence is proved through the actual square
integral. This supplies the representative map needed by completed
collar-energy extensions. No trace or chart transport estimate is assumed.
Actual Lean compilation pending.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT.LeviCivitaData.Dirichlet

universe u
variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem measurable_coordinateExtension_of_measurable
    (e : OpenPartialHomeomorph E M) {f : E → ℝ} (hf : Measurable f) :
    Measurable (coordinateExtension e f) := by
  apply measurable_of_restrict_of_restrict_compl e.open_target.measurableSet
  · have hc : Continuous (fun y : e.target => e.symm (y : M)) :=
      continuousOn_iff_continuous_restrict.mp e.symm.continuousOn
    convert hf.comp hc.measurable using 1
    funext y
    exact coordinateExtension_apply e f y.property
  · have hz : e.targetᶜ.domRestrict (coordinateExtension e f) = fun _ => (0 : ℝ) := by
      funext y
      exact indicator_of_notMem y.property _
    rw [hz]
    exact measurable_const

def nativeCompactChartFunction (e : OpenPartialHomeomorph E M) (K : Set E)
    (f : E → ℝ) : M → ℝ := coordinateExtension e (K.indicator f)

def nativeCompactChartFunctionLinear (e : OpenPartialHomeomorph E M) (K : Set E) :
    (E → ℝ) →ₗ[ℝ] (M → ℝ) where
  toFun := nativeCompactChartFunction e K
  map_add' f h := by
    funext y
    by_cases hy : y ∈ e.target <;> by_cases hx : e.symm y ∈ K <;>
      simp [nativeCompactChartFunction, coordinateExtension, hy, hx]
  map_smul' c f := by
    funext y
    by_cases hy : y ∈ e.target <;> by_cases hx : e.symm y ∈ K <;>
      simp [nativeCompactChartFunction, coordinateExtension, hy, hx]

theorem nativeCompactChartFunction_eq_of_tsupport_subset
    (e : OpenPartialHomeomorph E M) {K : Set E} {f : E → ℝ}
    (hs : tsupport f ⊆ K) : nativeCompactChartFunction e K f = coordinateExtension e f := by
  have hi : K.indicator f = f := by
    funext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))).symm
  rw [nativeCompactChartFunction, hi]

private theorem tsupport_compactIndicator_subset {K : Set E} (hK : IsCompact K)
    (f : E → ℝ) : tsupport (K.indicator f) ⊆ K := by
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hn
  exact hx (indicator_of_notMem hn _)

private theorem compactChart_density_continuousOn
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    ContinuousOn (g.pullbackVolumeDensity e) e.source := by
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  intro x hx
  exact (g.contDiffAt_pullbackVolumeDensity (he.contMDiffAt (e.open_source.mem_nhds hx))
    (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt

theorem exists_nativeCompactChartDensity_bound
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K, ‖g.pullbackVolumeDensity e x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((compactChart_density_continuousOn g e he hei).mono hKs)
  exact ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x hx => (hB x hx).trans (le_max_left _ _)⟩

def nativeCompactChartDensityBound
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) : ℝ :=
  (exists_nativeCompactChartDensity_bound g e he hei hK hKs).choose

theorem nativeCompactChartDensityBound_pos
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    0 < nativeCompactChartDensityBound g e he hei hK hKs :=
  (exists_nativeCompactChartDensity_bound g e he hei hK hKs).choose_spec.1

private theorem native_integrable_of_coordinate_density
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {F : M → ℝ} (hs : Function.support F ⊆ e.target)
    (hcoord : IntegrableOn (fun x => F (e x) * g.pullbackVolumeDensity e x) e.source) :
    Integrable F g.volumeMeasure := by
  have hd : AEMeasurable (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
      (volume.restrict e.source) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (compactChart_density_continuousOn g e he hei)).aemeasurable e.open_source.measurableSet
  have hw : Integrable (fun x => F (e x))
      ((volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict e.source) := by
    rw [restrict_withDensity e.open_source.measurableSet]
    apply (integrable_withDensity_iff_integrable_smul₀' hd (by simp)).mpr
    have hnon (x : E) : 0 ≤ g.pullbackVolumeDensity e x := Real.sqrt_nonneg _
    simpa only [IntegrableOn, ENNReal.toReal_ofReal (hnon _),
      smul_eq_mul, mul_comm] using! hcoord
  have hm := memLp_one_iff_integrable.mpr hw
  rw [← g.map_restrict_volumeMeasure_symm e he hei] at hm
  have ht := hm.comp_of_map (e.symm.continuousOn.aemeasurable e.open_target.measurableSet)
  have htarget : MemLp F 1 (g.volumeMeasure.restrict e.target) := by
    apply MemLp.ae_eq (hf_Lp := ht)
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    exact congrArg F (e.right_inv hy)
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    (memLp_one_iff_integrable.mp htarget)

private theorem integrableOn_square_density
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {f : E → ℝ} (hf2 : MemLp f 2 volume) :
    IntegrableOn (fun x => f x ^ 2 * g.pullbackVolumeDensity e x) K := by
  have hρ := ((compactChart_density_continuousOn g e he hei).mono hKs).aestronglyMeasurable
    (μ := (volume : Measure E)) hK.measurableSet
  have hb : ∀ᵐ x ∂volume.restrict K, ‖g.pullbackVolumeDensity e x‖ ≤
      nativeCompactChartDensityBound g e he hei hK hKs :=
    (ae_restrict_mem hK.measurableSet).mono fun x hx =>
      (exists_nativeCompactChartDensity_bound g e he hei hK hKs).choose_spec.2 x hx
  simpa only [mul_comm, IntegrableOn] using! hf2.integrable_sq.integrableOn.bdd_mul hρ hb

theorem memLp_nativeCompactChartFunction
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {f : E → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 volume) :
    MemLp (nativeCompactChartFunction e K f) 2 g.volumeMeasure := by
  have hm := measurable_coordinateExtension_of_measurable e (hf.indicator hK.measurableSet)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi := (integrable_indicator_iff hK.measurableSet).mpr
    (integrableOn_square_density g e he hei hK hKs hf2)
  apply native_integrable_of_coordinate_density g e he hei
  · intro y hy
    by_contra hn
    apply hy
    simp only [nativeCompactChartFunction, coordinateExtension, indicator_of_notMem hn,
      zero_pow (by decide : 2 ≠ 0)]
  · apply hi.integrableOn.congr
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
    change _ = nativeCompactChartFunction e K f (e x) ^ 2 * g.pullbackVolumeDensity e x
    rw [nativeCompactChartFunction, coordinateExtension_comp_apply e _ hx]
    by_cases h : x ∈ K <;> simp [h]

theorem integral_nativeCompactChart_square
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {f : E → ℝ} (hf : Measurable f) :
    (∫ y, nativeCompactChartFunction e K f y ^ 2 ∂g.volumeMeasure) =
      ∫ x in K, f x ^ 2 * g.pullbackVolumeDensity e x := by
  have hts := tsupport_compactIndicator_subset hK f
  have hc : HasCompactSupport (K.indicator f) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hts
  have hs : tsupport (nativeCompactChartFunction e K f) ⊆ e '' K :=
    (tsupport_coordinateExtension_subset_image e hc (hts.trans hKs)).trans (image_mono hts)
  have hm := measurable_coordinateExtension_of_measurable e (hf.indicator hK.measurableSet)
  calc
    _ = ∫ y in e '' K, nativeCompactChartFunction e K f y ^ 2 ∂g.volumeMeasure := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hy (hs ht)),
        zero_pow (by decide : 2 ≠ 0)]
    _ = ∫ x in K, nativeCompactChartFunction e K f (e x) ^ 2 *
        g.pullbackVolumeDensity e x :=
      integral_compact_image_eq_pullback_density (g := g) e he hei hK hKs (hm.pow_const 2)
    _ = _ := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      change nativeCompactChartFunction e K f (e x) ^ 2 *
        g.pullbackVolumeDensity e x = f x ^ 2 * g.pullbackVolumeDensity e x
      rw [nativeCompactChartFunction, coordinateExtension_comp_apply e _ (hKs hx),
        indicator_of_mem hx]

theorem integral_nativeCompactChart_square_le
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {f : E → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 volume) :
    (∫ y, nativeCompactChartFunction e K f y ^ 2 ∂g.volumeMeasure) ≤
      nativeCompactChartDensityBound g e he hei hK hKs * ∫ x : E, f x ^ 2 := by
  rw [integral_nativeCompactChart_square g e he hei hK hKs hf]
  let B := nativeCompactChartDensityBound g e he hei hK hKs
  calc
    _ ≤ ∫ x in K, B * f x ^ 2 :=
      setIntegral_mono_on (integrableOn_square_density g e he hei hK hKs hf2)
        (hf2.integrable_sq.const_mul B).integrableOn hK.measurableSet (fun x hx => by
          have hρ : g.pullbackVolumeDensity e x ≤ B := (le_abs_self _).trans
            ((exists_nativeCompactChartDensity_bound g e he hei hK hKs).choose_spec.2 x hx)
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left hρ (sq_nonneg (f x)))
    _ = B * ∫ x in K, f x ^ 2 := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hf2.integrable_sq (Eventually.of_forall fun x => sq_nonneg _))
      (nativeCompactChartDensityBound_pos g e he hei hK hKs).le

theorem nativeCompactChartFunction_congr_ae
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {f h : E → ℝ} (hf : Measurable f) (hh : Measurable h)
    (hf2 : MemLp f 2 volume) (hh2 : MemLp h 2 volume) (hfh : f =ᵐ[volume] h) :
    nativeCompactChartFunction e K f =ᵐ[g.volumeMeasure] nativeCompactChartFunction e K h := by
  have hsource : (∫ x : E, (f x - h x) ^ 2) = 0 := by
    calc
      _ = ∫ _ : E, (0 : ℝ) := integral_congr_ae (hfh.mono fun x hx => by simp [hx])
      _ = _ := integral_zero _ _
  have hbound := integral_nativeCompactChart_square_le g e he hei hK hKs
    (hf.sub hh) (hf2.sub hh2)
  have hz : (∫ y, nativeCompactChartFunction e K (f - h) y ^ 2 ∂g.volumeMeasure) = 0 := by
    apply le_antisymm _ (integral_nonneg fun y => sq_nonneg _)
    simpa only [Pi.sub_apply, hsource, mul_zero] using hbound
  have hi := (memLp_nativeCompactChartFunction g e he hei hK hKs
    (hf.sub hh) (hf2.sub hh2)).integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hz
  have hzero : nativeCompactChartFunction e K (f - h) =ᵐ[g.volumeMeasure] 0 :=
    hae.mono fun y hy => eq_zero_of_pow_eq_zero hy
  rw [show nativeCompactChartFunction e K (f - h) =
    nativeCompactChartFunction e K f - nativeCompactChartFunction e K h from
      (nativeCompactChartFunctionLinear e K).map_sub _ _] at hzero
  exact hzero.mono fun y hy => sub_eq_zero.mp hy

private theorem euclidean_nativeLp_memLp_volume
    (f : Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure) :
    MemLp (f : E → ℝ) 2 volume := by
  simpa only [native_euclideanMetric_volumeMeasure] using Lp.memLp f

def nativeCompactChartL2Linear
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure →ₗ[ℝ] Lp ℝ 2 g.volumeMeasure where
  toFun f := (memLp_nativeCompactChartFunction g e he hei hK hKs
    (Lp.stronglyMeasurable f).measurable (euclidean_nativeLp_memLp_volume f)).toLp _
  map_add' f h := by
    apply Lp.ext
    have hadd : (f + h : Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure)
        =ᵐ[volume] (f : E → ℝ) + h := by
      simpa only [native_euclideanMetric_volumeMeasure] using Lp.coeFn_add f h
    have hc := nativeCompactChartFunction_congr_ae g e he hei hK hKs
      (Lp.stronglyMeasurable (f + h)).measurable
      ((Lp.stronglyMeasurable f).measurable.add (Lp.stronglyMeasurable h).measurable)
      (euclidean_nativeLp_memLp_volume _) ((euclidean_nativeLp_memLp_volume f).add
        (euclidean_nativeLp_memLp_volume h)) hadd
    filter_upwards [(memLp_nativeCompactChartFunction g e he hei hK hKs
      (Lp.stronglyMeasurable (f + h)).measurable (euclidean_nativeLp_memLp_volume _)).coeFn_toLp,
      (memLp_nativeCompactChartFunction g e he hei hK hKs
        (Lp.stronglyMeasurable f).measurable (euclidean_nativeLp_memLp_volume f)).coeFn_toLp,
      (memLp_nativeCompactChartFunction g e he hei hK hKs
        (Lp.stronglyMeasurable h).measurable (euclidean_nativeLp_memLp_volume h)).coeFn_toLp,
      Lp.coeFn_add ((memLp_nativeCompactChartFunction g e he hei hK hKs
        (Lp.stronglyMeasurable f).measurable (euclidean_nativeLp_memLp_volume f)).toLp _)
        ((memLp_nativeCompactChartFunction g e he hei hK hKs
          (Lp.stronglyMeasurable h).measurable (euclidean_nativeLp_memLp_volume h)).toLp _), hc]
          with y hsum hf hh htarget hcongr
    rw [hsum, hcongr, show nativeCompactChartFunction e K ((f : E → ℝ) + h) =
      nativeCompactChartFunction e K f + nativeCompactChartFunction e K h from
        (nativeCompactChartFunctionLinear e K).map_add _ _, htarget]
    simp only [Pi.add_apply, hf, hh]
  map_smul' c f := by
    apply Lp.ext
    have hsm : (c • f : Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure)
        =ᵐ[volume] c • (f : E → ℝ) := by
      simpa only [native_euclideanMetric_volumeMeasure] using Lp.coeFn_smul c f
    have hc := nativeCompactChartFunction_congr_ae g e he hei hK hKs
      (Lp.stronglyMeasurable (c • f)).measurable ((Lp.stronglyMeasurable f).measurable.const_smul c)
      (euclidean_nativeLp_memLp_volume _) ((euclidean_nativeLp_memLp_volume f).const_smul c) hsm
    filter_upwards [(memLp_nativeCompactChartFunction g e he hei hK hKs
      (Lp.stronglyMeasurable (c • f)).measurable (euclidean_nativeLp_memLp_volume _)).coeFn_toLp,
      (memLp_nativeCompactChartFunction g e he hei hK hKs
        (Lp.stronglyMeasurable f).measurable (euclidean_nativeLp_memLp_volume f)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_nativeCompactChartFunction g e he hei hK hKs
        (Lp.stronglyMeasurable f).measurable (euclidean_nativeLp_memLp_volume f)).toLp _), hc]
          with y hcf hf htarget hcongr
    simp only [RingHom.id_apply]
    rw [hcf, hcongr, show nativeCompactChartFunction e K (c • (f : E → ℝ)) =
      c • nativeCompactChartFunction e K f from (nativeCompactChartFunctionLinear e K).map_smul _ _,
      htarget]
    simp only [Pi.smul_apply, smul_eq_mul, hf]

theorem nativeCompactChartL2Linear_ae
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (f : Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure) :
    (nativeCompactChartL2Linear g e he hei hK hKs f : M → ℝ) =ᵐ[g.volumeMeasure]
      nativeCompactChartFunction e K f :=
  (memLp_nativeCompactChartFunction g e he hei hK hKs (Lp.stronglyMeasurable f).measurable
    (euclidean_nativeLp_memLp_volume f)).coeFn_toLp

theorem nativeCompactChartL2Linear_norm_le
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (f : Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure) :
    ‖nativeCompactChartL2Linear g e he hei hK hKs f‖ ≤
      Real.sqrt (nativeCompactChartDensityBound g e he hei hK hKs) * ‖f‖ := by
  have htarget : ‖nativeCompactChartL2Linear g e he hei hK hKs f‖ ^ 2 =
      ∫ y, nativeCompactChartFunction e K f y ^ 2 ∂g.volumeMeasure := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [nativeCompactChartL2Linear_ae g e he hei hK hKs f] with y hy
    simp [hy, pow_two]
  have hsource : (∫ x : E, f x ^ 2) = ‖f‖ ^ 2 := by
    calc
      _ = ∫ x : E, f x ^ 2 ∂(RiemannianMetric.euclideanMetric 3).volumeMeasure :=
        (congrArg (fun μ : Measure E => ∫ x : E, (f : E → ℝ) x ^ 2 ∂μ)
          (native_euclideanMetric_volumeMeasure 3)).symm
      _ = _ := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by simp [pow_two]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [htarget, mul_pow,
    Real.sq_sqrt (nativeCompactChartDensityBound_pos g e he hei hK hKs).le, ← hsource]
  exact integral_nativeCompactChart_square_le g e he hei hK hKs
    (Lp.stronglyMeasurable f).measurable (euclidean_nativeLp_memLp_volume f)

def nativeCompactChartL2CLM
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure →L[ℝ] Lp ℝ 2 g.volumeMeasure :=
  (nativeCompactChartL2Linear g e he hei hK hKs).mkContinuous
    (Real.sqrt (nativeCompactChartDensityBound g e he hei hK hKs))
    (nativeCompactChartL2Linear_norm_le g e he hei hK hKs)

#print axioms memLp_nativeCompactChartFunction
#print axioms nativeCompactChartFunction_congr_ae
#print axioms nativeCompactChartL2Linear_norm_le

end Yamabe3.Analysis.SpherePolar
