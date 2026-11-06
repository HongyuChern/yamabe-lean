import Yamabe3.Analysis.EuclideanBoundaryCutoffEnergy
import Yamabe3.Analysis.NativeH1SphereTraceCore
import Yamabe3.Analysis.NativeChartSphereMetric

/-!
# The actual boundary-layer energy on the original manifold

All constants are chosen on one fixed compact chart collar, before its
thickness and the smooth native energy test. The volume density and the
coordinate derivative comparison are proved properties of that same
metric and chart. The endpoint uses the native volume of the metric
induced by the actual chart sphere immersion.

The estimate retains the original gradient energy in the shrinking
collar, rather than replacing it by the global energy. This is needed
to pass to a zero-trace cutoff limit. Completion and the actual exterior
zero extension are separate consumers.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold ENNReal

namespace Yamabe3.Analysis.EuclideanSphereTrace

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet NativeChartSphereMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- Actual native volume, native sphere area and native gradient energy
of one and the same smooth test. The constant precedes both δ and φ. -/
theorem exists_native_chart_boundary_layer_energy_bound
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a : ℝ} (ha : 0 < a)
    (hKs : sphereTraceAnnulus a (2 * a) ⊆ e.source)
    (hcoeff : ∀ x ∈ sphereTraceAnnulus a (2 * a),
      gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hGauss : ∀ x ∈ sphereTraceAnnulus a (2 * a), ∀ v : E,
      gE.inner x x v = inner ℝ x v)
    (hs : ∀ θ : S, GreenMass.SphereMeasure.dilation a θ ∈ e.source) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → 2 * δ ≤ a →
      ∀ φ : EnergyTest g.leviCivitaData univ,
      δ⁻¹ ^ 2 * (∫ y in e '' sphereTraceAnnulus a (a + 2 * δ), φ y ^ 2 ∂g.volumeMeasure) ≤
        C * (δ⁻¹ * (∫ θ : S, φ (e (a • (θ : E))) ^ 2
          ∂(chartRadiusMetric g e he hei a ha.ne' hs).volumeMeasure) +
          ∫ y in e '' sphereTraceAnnulus a (a + 2 * δ), g.inner y
            (g.leviCivitaData.gradient φ y) (g.leviCivitaData.gradient φ y)
            ∂g.volumeMeasure) := by
  let K := sphereTraceAnnulus a (2 * a)
  have hK : IsCompact K := isCompact_sphereTraceAnnulus a (2 * a)
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) K := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hKs hx)))
      (hD.mfderiv_injective (hKs hx))).1.continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcρ⟩ := exists_chart_density_lower_bound (g := g) e he hei hK hKs
  obtain ⟨A, hA, hAderiv⟩ := exists_chart_fderiv_sq_bound
    (g := g) (D := g.leviCivitaData) e he hK hKs
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hρ
  let B₀ := max B 0
  have hB₀ : 0 ≤ B₀ := le_max_right _ _
  have hρB (x : E) (hx : x ∈ K) : g.pullbackVolumeDensity e x ≤ B₀ := by
    have hb : |g.pullbackVolumeDensity e x| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB x hx
    exact (le_abs_self _).trans (hb.trans (le_max_left _ _))
  let C₁ := 16 * B₀ / c
  let C₂ := 64 * B₀ * A / c
  let C := C₁ + C₂ + 1
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδa φ
  let L := sphereTraceAnnulus a (a + 2 * δ)
  have hL : IsCompact L := isCompact_sphereTraceAnnulus a (a + 2 * δ)
  have hLK : L ⊆ K := by
    intro x hx
    exact ⟨hx.1, by linarith only [hx.2, hδa]⟩
  have hLs : L ⊆ e.source := hLK.trans hKs
  let f : E → ℝ := fun x => φ (e x)
  let G : M → ℝ := fun y => g.inner y
    (g.leviCivitaData.gradient φ y) (g.leviCivitaData.gradient φ y)
  have hfc : ContDiffOn ℝ ∞ f e.source := (φ.smooth.comp_contMDiffOn he).contDiffOn
  have hGc : Continuous G := g.leviCivitaData.continuous_inner_gradient φ.smooth φ.smooth
  have hGn (y : M) : 0 ≤ G y := by
    by_cases hz : g.leviCivitaData.gradient φ y = 0
    · simp [G, hz]
    · exact (g.pos y _ hz).le
  have hfi : IntegrableOn (fun x => f x ^ 2) L :=
    ((hfc.continuousOn.pow 2).mono hLs).integrableOn_compact hL
  have hdi : IntegrableOn (fun x => ‖fderiv ℝ f x‖ ^ 2) L :=
    (((hfc.continuousOn_fderiv_of_isOpen e.open_source (by simp)).norm.pow 2).mono hLs).integrableOn_compact hL
  have hfrhoi : IntegrableOn (fun x => f x ^ 2 * g.pullbackVolumeDensity e x) L :=
    (((hfc.continuousOn.pow 2).mono hLs).mul (hρ.mono hLK)).integrableOn_compact hL
  have hGrhoi : IntegrableOn (fun x => G (e x) * g.pullbackVolumeDensity e x) L :=
    ((hGc.comp_continuousOn (e.continuousOn.mono hLs)).mul (hρ.mono hLK)).integrableOn_compact hL
  have hvol : (∫ y in e '' L, φ y ^ 2 ∂g.volumeMeasure) ≤
      B₀ * ∫ x in L, f x ^ 2 := by
    have hmeas : Measurable (fun y : M => φ y ^ 2) := (φ.smooth.continuous.pow 2).measurable
    rw [integral_compact_image_eq_pullback_density (g := g) (F := fun y : M => φ y ^ 2)
      e he hei hL hLs hmeas, ← integral_const_mul]
    exact setIntegral_mono_on hfrhoi (hfi.const_mul _) hL.measurableSet fun x hx => by
      dsimp only [f]
      nlinarith only [mul_le_mul_of_nonneg_left (hρB x (hLK hx)) (sq_nonneg (φ (e x)))]
  have hgrad : (∫ x in L, ‖fderiv ℝ f x‖ ^ 2) ≤
      (A / c) * ∫ y in e '' L, G y ∂g.volumeMeasure := by
    rw [integral_compact_image_eq_pullback_density (g := g) (F := G) e he hei hL hLs hGc.measurable,
      ← integral_const_mul]
    apply setIntegral_mono_on hdi (hGrhoi.const_mul _) hL.measurableSet
    intro x hx
    have hd := hAderiv φ φ.smooth x (hLK hx)
    rw [(chartPullback_eventuallyEq e φ (hLs hx)).fderiv_eq] at hd
    change ‖fderiv ℝ f x‖ ^ 2 ≤ A * G (e x) at hd
    calc
      _ ≤ A * G (e x) := hd
      _ = (A / c) * (G (e x) * c) := by field_simp [hc.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcρ x (hLK hx)) (hGn (e x))) (by positivity)
  let μa := (chartRadiusMetric g e he hei a ha.ne' hs).volumeMeasure
  let νa := ENNReal.ofReal (a ^ 2) • angularVolume
  have hrad (θ : S) : a • (θ : E) ∈ K :=
    radial_mem_sphereTraceAnnulus ha (show a ∈ Icc a (2 * a) by constructor <;> linarith) θ
  have harea : μa = νa.withDensity (fun θ : S =>
      ENNReal.ofReal (g.pullbackVolumeDensity e (a • (θ : E)))) :=
    chartRadiusMetric_volume_eq_native_density g gE e he hei a ha.ne' hs
      (fun θ => hcoeff _ (hrad θ)) (fun θ => hGauss _ (hrad θ))
  have hmeasure : ENNReal.ofReal c • νa ≤ μa := by
    rw [harea, ← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun θ =>
      ENNReal.ofReal_le_ofReal (hcρ _ (hrad θ)))
  have htcont : Continuous (fun θ : S => φ (e (a • (θ : E)))) :=
    SpherePolar.continuous_nativeSphereRestriction g e a hs φ
  have hti : Integrable (fun θ : S => φ (e (a • (θ : E))) ^ 2) μa := by
    simpa only [integrableOn_univ, Pi.pow_apply] using!
      (htcont.pow 2).continuousOn.integrableOn_compact
        (μ := μa) (isCompact_univ : IsCompact (univ : Set S))
  have htrace : (∫ θ : S, φ (e (a • (θ : E))) ^ 2 ∂νa) ≤
      (∫ θ : S, φ (e (a • (θ : E))) ^ 2 ∂μa) / c := by
    have h := integral_mono_measure hmeasure
      (Eventually.of_forall fun θ => sq_nonneg (φ (e (a • (θ : E))))) hti
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul] at h
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using h
  have hTn : 0 ≤ ∫ θ : S, φ (e (a • (θ : E))) ^ 2 ∂μa :=
    integral_nonneg fun θ => sq_nonneg _
  have hEn : 0 ≤ ∫ y in e '' L, G y ∂g.volumeMeasure := integral_nonneg hGn
  have hEuclidean := integral_boundary_layer_sq_le_trace_and_derivative
    ha hδ hδa e.open_source hLs hfc
  calc
    _ ≤ δ⁻¹ ^ 2 * (B₀ * ∫ x in L, f x ^ 2) :=
      mul_le_mul_of_nonneg_left hvol (sq_nonneg _)
    _ = B₀ * (δ⁻¹ ^ 2 * ∫ x in L, f x ^ 2) := by ring
    _ ≤ B₀ * ((16 / δ) * (∫ θ : S, φ (e (a • (θ : E))) ^ 2 ∂νa) +
        64 * ∫ x in L, ‖fderiv ℝ f x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hEuclidean hB₀
    _ ≤ B₀ * ((16 / δ) * ((∫ θ : S, φ (e (a • (θ : E))) ^ 2 ∂μa) / c) +
        64 * ((A / c) * ∫ y in e '' L, G y ∂g.volumeMeasure)) := by
      apply mul_le_mul_of_nonneg_left _ hB₀
      exact add_le_add (mul_le_mul_of_nonneg_left htrace (by positivity))
        (mul_le_mul_of_nonneg_left hgrad (by norm_num))
    _ = C₁ * (δ⁻¹ * ∫ θ : S, φ (e (a • (θ : E))) ^ 2 ∂μa) +
        C₂ * (∫ y in e '' L, G y ∂g.volumeMeasure) := by dsimp [C₁, C₂]; ring
    _ ≤ C * (δ⁻¹ * (∫ θ : S, φ (e (a • (θ : E))) ^ 2 ∂μa) +
        ∫ y in e '' L, G y ∂g.volumeMeasure) := by
      rw [mul_add]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (show C₁ ≤ C by dsimp [C]; linarith)
          (mul_nonneg (inv_pos.mpr hδ).le hTn))
        (mul_le_mul_of_nonneg_right (show C₂ ≤ C by dsimp [C]; linarith) hEn)

#print axioms exists_native_chart_boundary_layer_energy_bound

end Yamabe3.Analysis.EuclideanSphereTrace
