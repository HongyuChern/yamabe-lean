import Yamabe3.Analysis.NativeH1SphereTraceCore
import Yamabe3.Analysis.NativeChartSphereMetric
import Yamabe3.Analysis.NativeGaussSphereTrace

/-!
# The completed native H1 trace in the actual chart-sphere area space

The target is L2 for the metric induced from the original manifold by its
literal chart sphere map. Its measure is identified from the same extended
coordinate metric. A proved density domination transfers the already
constructed H1 trace into this physical space, including its smooth
representative and radius-dependent norm bound. The same operator kills
domain H1-zero inclusions when the boundary sphere is excluded.

Only this inclusion in the trace kernel is asserted. Equality of the trace
kernel and H1-zero, and agreement with weak conormal, remain separate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Topology Manifold ContDiff ENNReal

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT.LeviCivitaData.Dirichlet
open NativeChartSphereMetric GreenMass.NativeGaussSphereArea

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- Domination is derived for the actual induced metric, not supplied as
a replacement for geometric boundary measure. -/
theorem chartRadiusMetric_volume_le_nativeAngular
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r C : ℝ} (hr : r ≠ 0) (hC : 0 ≤ C)
    (hs : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (hcoeff : ∀ θ : S, gE.euclideanCoefficients (r • (θ : E)) =
      g.pullbackCoefficients e (r • (θ : E)))
    (hGauss : ∀ (θ : S) (w : E), gE.inner (r • (θ : E)) (r • (θ : E)) w =
      inner ℝ (r • (θ : E)) w)
    (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (r • (θ : E)) ≤ C) :
    (chartRadiusMetric g e he hei r hr hs).volumeMeasure ≤
      ENNReal.ofReal (C * r ^ 2) • angularVolume := by
  rw [chartRadiusMetric_eq_gaussRadiusMetric g gE e he hei r hr hs hcoeff,
    gaussRadiusMetric_volume_eq_weighted_polarArea gE r hr hGauss]
  calc
    _ ≤ (ENNReal.ofReal (r ^ 2) • (volume : Measure E).toSphere).withDensity
        (fun _ : S => ENNReal.ofReal C) :=
      withDensity_mono (Eventually.of_forall fun θ => ENNReal.ofReal_le_ofReal (hρ θ))
    _ = _ := by
      rw [withDensity_const, smul_smul, ← ENNReal.ofReal_mul hC,
        polar_sphereMeasure_eq_native]

/-- The completed trace takes values in the actual manifold-sphere L2
space. The explicit factor is `r sqrt(C)` times the proved native H1 trace
bound. The construction gives the same literal restriction on smooth
tests and annihilates actual domain H1-zero elements. -/
theorem exists_native_physical_sphere_trace
    [CompactSpace M] [ConnectedSpace M]
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a b r C : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    (hKs : sphereTraceAnnulus a b ⊆ e.source) (hC : 0 ≤ C)
    (hcoeff : ∀ θ : S, gE.euclideanCoefficients (r • (θ : E)) =
      g.pullbackCoefficients e (r • (θ : E)))
    (hGauss : ∀ (θ : S) (w : E), gE.inner (r • (θ : E)) (r • (θ : E)) w =
      inner ℝ (r • (θ : E)) w)
    (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (r • (θ : E)) ≤ C) :
    ∃ T : H1Zero g.leviCivitaData univ →L[ℝ]
        Lp ℝ 2 (chartRadiusMetric g e he hei r (ha.trans_le hr.1).ne'
          (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ))).volumeMeasure,
      (∀ φ : EnergyTest g.leviCivitaData univ,
        (T (φ : H1Zero g.leviCivitaData univ) : S → ℝ) =ᵐ[
          (chartRadiusMetric g e he hei r (ha.trans_le hr.1).ne'
            (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ))).volumeMeasure]
          nativeSphereRestriction e r φ) ∧
      (∀ w : H1Zero g.leviCivitaData univ,
        ‖T w‖ ≤ (r * Real.sqrt C * nativeSphereTraceBound g e he hei a b hKs) * ‖w‖) ∧
      (∀ (Ω : Set M), (∀ θ : S, e (r • (θ : E)) ∉ Ω) →
        ∀ w : H1Zero g.leviCivitaData Ω, T (nativeDomainEnergyInclusion g Ω w) = 0) := by
  have hrpos : 0 < r := ha.trans_le hr.1
  let hs : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source :=
    fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)
  let μ := (chartRadiusMetric g e he hei r hrpos.ne' hs).volumeMeasure
  have hμ : μ ≤ ENNReal.ofReal (C * r ^ 2) • angularVolume :=
    chartRadiusMetric_volume_le_nativeAngular g gE e he hei hrpos.ne' hC hs hcoeff hGauss hρ
  let J : Lp ℝ 2 angularVolume →L[ℝ] Lp ℝ 2 μ :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hμ
  let A := nativeSphereTraceCLM g e he hei ha hab hr hKs
  refine ⟨J.comp A, ?_, ?_, ?_⟩
  · intro φ
    have hj := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hμ
      (A (φ : H1Zero g.leviCivitaData univ))
    have haeq : (A (φ : H1Zero g.leviCivitaData univ) : S → ℝ) =ᵐ[angularVolume]
        nativeSphereRestriction e r φ := by
      dsimp only [A]
      rw [nativeSphereTraceCLM_coe]
      exact nativeSphereTestTraceLinear_ae g e r hs φ
    exact hj.trans ((Measure.absolutelyContinuous_of_le_smul hμ).ae_eq haeq)
  · intro w
    have hJn : ‖J‖ ≤ r * Real.sqrt C := by
      have h := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := (2 : ℝ≥0∞))
        ENNReal.ofReal_ne_top hμ
      have hc : 0 ≤ C * r ^ 2 := mul_nonneg hC (sq_nonneg r)
      norm_num only [ENNReal.toReal_ofReal hc, ENNReal.toReal_div, ENNReal.toReal_one,
        ENNReal.toReal_ofNat] at h
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hC, Real.sqrt_sq hrpos.le] at h
      simpa only [J, mul_comm] using! h
    calc
      ‖(J.comp A) w‖ ≤ ‖J‖ * ‖A w‖ := J.le_opNorm (A w)
      _ ≤ (r * Real.sqrt C) *
          (nativeSphereTraceBound g e he hei a b hKs * ‖w‖) :=
        mul_le_mul hJn (nativeSphereTraceCLM_norm_le g e he hei ha hab hr hKs w)
          (norm_nonneg _) (mul_nonneg hrpos.le (Real.sqrt_nonneg _))
      _ = _ := by ring
  · intro Ω hout w
    change J (A (nativeDomainEnergyInclusion g Ω w)) = 0
    rw [show A (nativeDomainEnergyInclusion g Ω w) = 0 from
      nativeSphereTraceCLM_domainInclusion_zero g e he hei ha hab hr hKs Ω hout w,
      map_zero]

#print axioms chartRadiusMetric_volume_le_nativeAngular
#print axioms exists_native_physical_sphere_trace

end Yamabe3.Analysis.SpherePolar
