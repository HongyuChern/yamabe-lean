import Yamabe3.Analysis.NativeSmoothSphereTrace
import Yamabe3.Analysis.NativeDomainEnergyInclusionCore
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Compactness.ChartEnergy
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateEnergy

/-!
# Actual H1 sphere trace without angular spectral dependencies

The same recovered trace construction now has only its necessary parents:
actual coordinate energy comparison, radial FTC, and the native H1 completion.
It constructs the continuous linear trace from literal smooth restrictions,
and proves H1-zero domain inclusions have zero trace on excluded spheres.
The measure is explicitly the native angularVolume. The separate
NativeSphereTraceDirichlet extension retains the inverse-specific trace theorem.

This proves H1-zero is contained in the trace kernel, not equality of the
kernel with H1-zero. Angular collar and matching assertions remain separate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory PoincareMT UniformSpace Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

private def sphereTraceNativeTestNormedSpace (g : RiemannianMetric 3 M) (Ω : Set M) :
    NormedSpace ℝ (EnergyTest g.leviCivitaData Ω) := inferInstance
private def sphereTraceNativeH1NormedSpace (g : RiemannianMetric 3 M) (Ω : Set M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData Ω) := inferInstance
attribute [local instance] sphereTraceNativeTestNormedSpace sphereTraceNativeH1NormedSpace

/-- The metric-dependent constant precedes every native energy test.
The test need not have support in this chart. -/
theorem exists_native_chart_restriction_energy_bound
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : EnergyTest g.leviCivitaData univ,
      (∫ x in K, sphereTraceEnergyDensity (fun y => φ (e y)) x) ≤ C * ‖φ‖ ^ 2 := by
  obtain ⟨A, hA, hderiv⟩ := exists_chart_fderiv_sq_bound
    (g := g) (D := g.leviCivitaData) e he hK hKs
  obtain ⟨c, hc, hdensity⟩ := exists_chart_density_lower_bound (g := g) e he hei hK hKs
  let C : ℝ := (1 + A) / c
  have hC : 0 < C := div_pos (by linarith only [hA]) hc
  have hCc : C * c = 1 + A := by dsimp only [C]; exact div_mul_cancel₀ _ hc.ne'
  refine ⟨C, hC, fun φ => ?_⟩
  let G : M → ℝ := fun y => g.inner y
    (g.leviCivitaData.gradient φ y) (g.leviCivitaData.gradient φ y)
  let F : M → ℝ := fun y => φ y ^ 2 + G y
  have hGc : Continuous G := g.leviCivitaData.continuous_inner_gradient φ.smooth φ.smooth
  have hGi : Integrable G g.volumeMeasure := φ.integrable_gradient φ
  have hGn (y : M) : 0 ≤ G y := by
    by_cases hz : g.leviCivitaData.gradient φ y = 0
    · simp [G, hz]
    · exact (g.pos y _ hz).le
  have hFn (y : M) : 0 ≤ F y := add_nonneg (sq_nonneg _) (hGn y)
  have hFc : Continuous F := (φ.smooth.continuous.pow 2).add hGc
  have hFi : Integrable F g.volumeMeasure := φ.memLp.integrable_sq.add hGi
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) K := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hKs hx)))
      (hD.mfderiv_injective (hKs hx))).1.continuousAt.continuousWithinAt
  have hφ : ContDiffOn ℝ ∞ (fun y => φ (e y)) e.source :=
    (φ.smooth.comp_contMDiffOn he).contDiffOn
  have hqc : ContinuousOn (sphereTraceEnergyDensity (fun y => φ (e y))) e.source := by
    simpa only [sphereTraceEnergyDensity, Pi.pow_apply, Pi.add_apply] using!
      (hφ.continuousOn.pow 2).add
        ((hφ.continuousOn_fderiv_of_isOpen e.open_source (by simp)).norm.pow 2)
  have hqi : IntegrableOn (sphereTraceEnergyDensity (fun y => φ (e y))) K :=
    (hqc.mono hKs).integrableOn_compact hK
  have hFcρ : ContinuousOn (fun x => F (e x) * g.pullbackVolumeDensity e x) K :=
    (hFc.comp_continuousOn (e.continuousOn.mono hKs)).mul hρ
  have hpoint (x : E) (hx : x ∈ K) :
      sphereTraceEnergyDensity (fun y => φ (e y)) x ≤
        C * (F (e x) * g.pullbackVolumeDensity e x) := by
    have hd := hderiv φ φ.smooth x hx
    rw [(chartPullback_eventuallyEq e φ (hKs hx)).fderiv_eq] at hd
    change ‖fderiv ℝ (fun y => φ (e y)) x‖ ^ 2 ≤ A * G (e x) at hd
    calc
      _ ≤ (1 + A) * F (e x) := by
        dsimp only [sphereTraceEnergyDensity, F]
        nlinarith only [hd, hGn (e x), mul_nonneg hA (sq_nonneg (φ (e x)))]
      _ = C * (F (e x) * c) := by rw [← hCc]; ring
      _ ≤ C * (F (e x) * g.pullbackVolumeDensity e x) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hdensity x hx) (hFn (e x))) hC.le
  calc
    _ ≤ ∫ x in K, C * (F (e x) * g.pullbackVolumeDensity e x) :=
      setIntegral_mono_on hqi ((continuousOn_const.mul hFcρ).integrableOn_compact hK)
        hK.measurableSet hpoint
    _ = C * ∫ y in e '' K, F y ∂g.volumeMeasure := by
      rw [integral_const_mul,
        integral_compact_image_eq_pullback_density e he hei hK hKs hFc.measurable]
    _ ≤ C * ∫ y, F y ∂g.volumeMeasure :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hFi (Eventually.of_forall hFn)) hC.le
    _ = C * ‖φ‖ ^ 2 := by
      congr 1
      rw [φ.norm_sq, integral_add φ.memLp.integrable_sq hGi]
      simp only [pow_two, G, energyInner]

def nativeSphereRestriction (e : OpenPartialHomeomorph E M) (r : ℝ) (f : M → ℝ) : S → ℝ :=
  fun θ => f (e (r • (θ : E)))

theorem continuous_nativeSphereRestriction (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M) (r : ℝ)
    (hs : ∀ θ : S, r • (θ : E) ∈ e.source) (φ : EnergyTest g.leviCivitaData univ) :
    Continuous (nativeSphereRestriction e r φ) := by
  apply φ.smooth.continuous.comp
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hc : ContinuousAt (fun q : S => r • (q : E)) θ := by
    simpa only [Pi.smul_apply] using!
      ((continuous_const : Continuous (fun _ : S => r)).smul
        (continuous_subtype_val : Continuous (Subtype.val : S → E))).continuousAt (x := θ)
  exact ContinuousAt.comp (f := fun q : S => r • (q : E))
    (e.continuousOn.continuousAt (e.open_source.mem_nhds (hs θ))) hc

theorem memLp_nativeSphereRestriction (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M) (r : ℝ)
    (hs : ∀ θ : S, r • (θ : E) ∈ e.source) (φ : EnergyTest g.leviCivitaData univ) :
    MemLp (nativeSphereRestriction e r φ) 2 angularVolume := by
  have h := continuous_nativeSphereRestriction g e r hs φ
  apply (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mpr
  simpa only [IntegrableOn, Measure.restrict_univ, Pi.pow_apply] using!
    (h.pow 2).continuousOn.integrableOn_compact (μ := angularVolume) isCompact_univ

def nativeSphereTestTraceLinear (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M) (r : ℝ) (hs : ∀ θ : S, r • (θ : E) ∈ e.source) :
    EnergyTest g.leviCivitaData univ →ₗ[ℝ] Lp ℝ 2 angularVolume where
  toFun φ := (memLp_nativeSphereRestriction g e r hs φ).toLp (nativeSphereRestriction e r φ)
  map_add' φ ψ := MemLp.toLp_add
    (memLp_nativeSphereRestriction g e r hs φ) (memLp_nativeSphereRestriction g e r hs ψ)
  map_smul' c φ := MemLp.toLp_const_smul c (memLp_nativeSphereRestriction g e r hs φ)

theorem nativeSphereTestTraceLinear_ae (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M) (r : ℝ) (hs : ∀ θ : S, r • (θ : E) ∈ e.source)
    (φ : EnergyTest g.leviCivitaData univ) :
    (nativeSphereTestTraceLinear g e r hs φ : S → ℝ) =ᵐ[angularVolume]
      nativeSphereRestriction e r φ := (memLp_nativeSphereRestriction g e r hs φ).coeFn_toLp

theorem nativeSphereTestTraceLinear_norm_sq (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M) (r : ℝ) (hs : ∀ θ : S, r • (θ : E) ∈ e.source)
    (φ : EnergyTest g.leviCivitaData univ) :
    ‖nativeSphereTestTraceLinear g e r hs φ‖ ^ 2 =
      ∫ θ : S, φ (e (r • (θ : E))) ^ 2 ∂angularVolume := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [nativeSphereTestTraceLinear_ae g e r hs φ] with θ hθ
  simp only [hθ, RCLike.inner_apply, conj_trivial, nativeSphereRestriction, pow_two]

def nativeSphereTraceBound (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (a b : ℝ) (hKs : sphereTraceAnnulus a b ⊆ e.source) : ℝ :=
  Real.sqrt ((((b - a)⁻¹ + 1) / a ^ 2) *
    (exists_native_chart_restriction_energy_bound g e he hei
      (isCompact_sphereTraceAnnulus a b) hKs).choose)

theorem nativeSphereTestTraceLinear_norm_le (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    (hKs : sphereTraceAnnulus a b ⊆ e.source) (φ : EnergyTest g.leviCivitaData univ) :
    ‖nativeSphereTestTraceLinear g e r (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)) φ‖ ≤
      nativeSphereTraceBound g e he hei a b hKs * ‖φ‖ := by
  let h := exists_native_chart_restriction_energy_bound g e he hei
    (isCompact_sphereTraceAnnulus a b) hKs
  have hl : 0 < b - a := sub_pos.mpr hab
  have hcoef : 0 ≤ ((b - a)⁻¹ + 1) / a ^ 2 := by positivity
  have hfirst := integral_sphere_restriction_sq_le_annulus_energy ha hab hr
    e.open_source hKs (φ.smooth.comp_contMDiffOn he).contDiffOn
  have hsecond := mul_le_mul_of_nonneg_left (h.choose_spec.2 φ) hcoef
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg φ))).mp
  rw [nativeSphereTestTraceLinear_norm_sq]
  have hp : 0 ≤ (((b - a)⁻¹ + 1) / a ^ 2) * h.choose :=
    mul_nonneg hcoef h.choose_spec.1.le
  simpa only [nativeSphereTraceBound, mul_pow, Real.sq_sqrt hp, mul_assoc,
    Function.comp_def] using! hfirst.trans hsecond

def nativeSphereTestTraceCLM (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    (hKs : sphereTraceAnnulus a b ⊆ e.source) :
    EnergyTest g.leviCivitaData univ →L[ℝ] Lp ℝ 2 angularVolume :=
  (nativeSphereTestTraceLinear g e r (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ))).mkContinuous
      (nativeSphereTraceBound g e he hei a b hKs)
      (nativeSphereTestTraceLinear_norm_le g e he hei ha hab hr hKs)

/-- The value trace is the continuous extension of literal smooth
restriction, constructed from the actual metric estimate above. -/
def nativeSphereTraceCLM (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    (hKs : sphereTraceAnnulus a b ⊆ e.source) :
    H1Zero g.leviCivitaData univ →L[ℝ] Lp ℝ 2 angularVolume :=
  (nativeSphereTestTraceCLM g e he hei ha hab hr hKs).extend Completion.toComplL

@[simp] theorem nativeSphereTraceCLM_coe (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    (hKs : sphereTraceAnnulus a b ⊆ e.source) (φ : EnergyTest g.leviCivitaData univ) :
    nativeSphereTraceCLM g e he hei ha hab hr hKs (φ : H1Zero g.leviCivitaData univ) =
      nativeSphereTestTraceLinear g e r (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)) φ :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe (EnergyTest g.leviCivitaData univ)) φ

theorem nativeSphereTraceCLM_norm_le (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    (hKs : sphereTraceAnnulus a b ⊆ e.source) (w : H1Zero g.leviCivitaData univ) :
    ‖nativeSphereTraceCLM g e he hei ha hab hr hKs w‖ ≤
      nativeSphereTraceBound g e he hei a b hKs * ‖w‖ := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_le (nativeSphereTraceCLM g e he hei ha hab hr hKs).continuous.norm
      (continuous_const.mul continuous_norm)
  | ih φ =>
    rw [nativeSphereTraceCLM_coe, Completion.norm_coe]
    exact nativeSphereTestTraceLinear_norm_le g e he hei ha hab hr hKs φ


section Domain

variable [CompactSpace M] [ConnectedSpace M]

/-- True compactly supported domain tests vanish on the sphere, and
continuity passes this zero trace to every actual H1-zero element. -/
theorem nativeSphereTraceCLM_domainInclusion_zero (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    (hKs : sphereTraceAnnulus a b ⊆ e.source) (Ω : Set M)
    (houtside : ∀ θ : S, e (r • (θ : E)) ∉ Ω) (w : H1Zero g.leviCivitaData Ω) :
    nativeSphereTraceCLM g e he hei ha hab hr hKs (nativeDomainEnergyInclusion g Ω w) = 0 := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((nativeSphereTraceCLM g e he hei ha hab hr hKs).continuous.comp
        (nativeDomainEnergyInclusion g Ω).continuous) continuous_const
  | ih φ =>
    rw [nativeDomainEnergyInclusion_coe, nativeSphereTraceCLM_coe]
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [nativeSphereTestTraceLinear_ae g e r
      (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ))
      (nativeDomainTestInclusion g Ω φ)] with θ hθ
    rw [hθ]
    change φ (e (r • (θ : E))) = 0
    exact image_eq_zero_of_notMem_tsupport (fun ht => houtside θ (φ.support_subset ht))



end Domain

#print axioms exists_native_chart_restriction_energy_bound
#print axioms nativeSphereTraceCLM_norm_le
#print axioms nativeSphereTraceCLM_domainInclusion_zero

end Yamabe3.Analysis.SpherePolar
