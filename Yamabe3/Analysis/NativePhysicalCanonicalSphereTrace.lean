import Yamabe3.Analysis.NativeH1PhysicalSphereTrace
import Yamabe3.Analysis.NativeLocalCanonicalSphereTrace

/-!
# The canonical native H1 trace in the actual induced sphere area

The existing physical trace existence theorem supplies a bounded map into
L2 for the metric induced from the original manifold by the literal sphere
parametrization. This file names that map and proves that its actual test
restrictions determine it uniquely. It is exactly the proved change of
measure applied to the native angular trace.

A smooth representative on an open neighborhood of the sphere therefore
has the literal trace of the same completed H1 element for the physical
area measure. The representative need not be smooth away from that
neighborhood. No ambient almost-everywhere statement is restricted to the
sphere, and no equality of the trace kernel with H1-zero is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Topology Manifold ContDiff ENNReal

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT.LeviCivitaData.Dirichlet NativeChartSphereMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def physicalCanonicalSphereH1NormedSpace (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] physicalCanonicalSphereH1NormedSpace

variable (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
  (e : OpenPartialHomeomorph E M)
  (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  {a b r C : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
  (hKs : sphereTraceAnnulus a b ⊆ e.source) (hC : 0 ≤ C)
  (hcoeff : ∀ θ : S, gE.euclideanCoefficients (r • (θ : E)) =
    g.pullbackCoefficients e (r • (θ : E)))
  (hGauss : ∀ (θ : S) (v : E), gE.inner (r • (θ : E)) (r • (θ : E)) v =
    inner ℝ (r • (θ : E)) v)
  (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (r • (θ : E)) ≤ C)

/-- The existing proved physical trace, as a public continuous linear map.
Its codomain is the volume of the genuine original-manifold induced metric. -/
def nativePhysicalSphereTraceCLM :
    H1Zero g.leviCivitaData univ →L[ℝ] Lp ℝ 2 (chartRadiusMetric g e he hei r (ha.trans_le hr.1).ne'
      (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ))).volumeMeasure :=
  (exists_native_physical_sphere_trace g gE e he hei ha hab hr hKs hC
    hcoeff hGauss hρ).choose

theorem nativePhysicalSphereTraceCLM_coe_ae
    (φ : EnergyTest g.leviCivitaData univ) :
    (nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ
      (φ : H1Zero g.leviCivitaData univ) : S → ℝ) =ᵐ[(chartRadiusMetric g e he hei r (ha.trans_le hr.1).ne'
      (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ))).volumeMeasure]
        nativeSphereRestriction e r φ :=
  (exists_native_physical_sphere_trace g gE e he hei ha hab hr hKs hC
    hcoeff hGauss hρ).choose_spec.1 φ

theorem nativePhysicalSphereTraceCLM_norm_le
    (w : H1Zero g.leviCivitaData univ) :
    ‖nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ w‖ ≤
      (r * Real.sqrt C * nativeSphereTraceBound g e he hei a b hKs) * ‖w‖ :=
  (exists_native_physical_sphere_trace g gE e he hei ha hab hr hKs hC
    hcoeff hGauss hρ).choose_spec.2.1 w

theorem nativePhysicalSphereTraceCLM_domainInclusion_zero
    (Ω : Set M) (hout : ∀ θ : S, e (r • (θ : E)) ∉ Ω)
    (w : H1Zero g.leviCivitaData Ω) :
    nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ
      (nativeDomainEnergyInclusion g Ω w) = 0 :=
  (exists_native_physical_sphere_trace g gE e he hei ha hab hr hKs hC
    hcoeff hGauss hρ).choose_spec.2.2 Ω hout w

/-- Literal smooth-test restrictions determine the physical trace uniquely.
The proof uses the actual energy completion and continuity of both maps. -/
theorem nativePhysicalSphereTraceCLM_unique
    (T : H1Zero g.leviCivitaData univ →L[ℝ] Lp ℝ 2 (chartRadiusMetric g e he hei r (ha.trans_le hr.1).ne'
      (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ))).volumeMeasure)
    (hT : ∀ φ : EnergyTest g.leviCivitaData univ,
      (T (φ : H1Zero g.leviCivitaData univ) : S → ℝ) =ᵐ[(chartRadiusMetric g e he hei r (ha.trans_le hr.1).ne'
      (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ))).volumeMeasure]
        nativeSphereRestriction e r φ) :
    T = nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ := by
  apply ContinuousLinearMap.ext
  intro w
  induction w using Completion.induction_on with
  | hp =>
      exact isClosed_eq T.continuous
        (nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC
          hcoeff hGauss hρ).continuous
  | ih φ =>
      apply Lp.ext
      exact (hT φ).trans
        (nativePhysicalSphereTraceCLM_coe_ae g gE e he hei ha hab hr hKs hC
          hcoeff hGauss hρ φ).symm

/-- The named physical trace is exactly the actual angular trace followed
by the canonical map induced by the proved measure domination. -/
theorem nativePhysicalSphereTraceCLM_eq_measureChange :
    nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ =
      (Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := (2 : ℝ≥0∞))
        ENNReal.ofReal_ne_top
        (chartRadiusMetric_volume_le_nativeAngular g gE e he hei
          (ha.trans_le hr.1).ne' hC
          (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)) hcoeff hGauss hρ)).comp
            (nativeSphereTraceCLM g e he hei ha hab hr hKs) := by
  symm
  apply nativePhysicalSphereTraceCLM_unique g gE e he hei ha hab hr hKs hC
    hcoeff hGauss hρ
  intro φ
  have hμ := chartRadiusMetric_volume_le_nativeAngular g gE e he hei
    (ha.trans_le hr.1).ne' hC
    (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)) hcoeff hGauss hρ
  have hj := Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℝ) (p := (2 : ℝ≥0∞))
    ENNReal.ofReal_ne_top hμ
      (nativeSphereTraceCLM g e he hei ha hab hr hKs
        (φ : H1Zero g.leviCivitaData univ))
  have haeq : (nativeSphereTraceCLM g e he hei ha hab hr hKs
      (φ : H1Zero g.leviCivitaData univ) : S → ℝ) =ᵐ[angularVolume]
        nativeSphereRestriction e r φ := by
    rw [nativeSphereTraceCLM_coe]
    exact nativeSphereTestTraceLinear_ae g e r
      (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)) φ
  exact hj.trans ((Measure.absolutelyContinuous_of_le_smul hμ).ae_eq haeq)

/-- For every completed element the physical and angular traces are the
same actual function almost everywhere for the physical sphere area. -/
theorem nativePhysicalSphereTraceCLM_ae_angularTrace
    (w : H1Zero g.leviCivitaData univ) :
    (nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ w : S → ℝ)
      =ᵐ[(chartRadiusMetric g e he hei r (ha.trans_le hr.1).ne'
      (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ))).volumeMeasure] (nativeSphereTraceCLM g e he hei ha hab hr hKs w : S → ℝ) := by
  rw [nativePhysicalSphereTraceCLM_eq_measureChange]
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℝ) (p := (2 : ℝ≥0∞))
    ENNReal.ofReal_ne_top
    (chartRadiusMetric_volume_le_nativeAngular g gE e he hei
      (ha.trans_le hr.1).ne' hC
      (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)) hcoeff hGauss hρ)
      (nativeSphereTraceCLM g e he hei ha hab hr hKs w)

/-- The same locally smooth representative has its literal value trace
for the actual original-manifold induced sphere area. -/
theorem nativePhysicalSphereTraceCLM_of_locally_smooth_representative
    (w : H1Zero g.leviCivitaData univ) {U : Set M} (hU : IsOpen U) (W : M → ℝ)
    (hW : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ W U)
    (hae : W =ᵐ[g.volumeMeasure.restrict U]
      (toL2 g.leviCivitaData univ w : M → ℝ))
    (hSphereU : ∀ θ : S, e (r • (θ : E)) ∈ U) :
    (nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ w : S → ℝ)
      =ᵐ[(chartRadiusMetric g e he hei r (ha.trans_le hr.1).ne'
      (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ))).volumeMeasure] nativeSphereRestriction e r W := by
  have hAngular := nativeSphereTraceCLM_of_locally_smooth_representative
    g w hU W hW hae e he hei ha hab hr hKs hSphereU
  have hμ := chartRadiusMetric_volume_le_nativeAngular g gE e he hei
    (ha.trans_le hr.1).ne' hC
    (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)) hcoeff hGauss hρ
  exact (nativePhysicalSphereTraceCLM_ae_angularTrace g gE e he hei ha hab hr hKs
    hC hcoeff hGauss hρ w).trans
      ((Measure.absolutelyContinuous_of_le_smul hμ).ae_eq hAngular)

#print axioms nativePhysicalSphereTraceCLM
#print axioms nativePhysicalSphereTraceCLM_unique
#print axioms nativePhysicalSphereTraceCLM_eq_measureChange
#print axioms nativePhysicalSphereTraceCLM_of_locally_smooth_representative

end Yamabe3.Analysis.SpherePolar
