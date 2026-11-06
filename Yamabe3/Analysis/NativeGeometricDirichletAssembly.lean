import Yamabe3.Analysis.NativeForcedDirichletDataAssembly
import Yamabe3.Analysis.Green.NativeNormalDensity

/-!
# Geometry and forced conformal Dirichlet data from the original metric

The normal chart, Gauss extension, positive radius and physical area bound
are produced from g and p, before any source or lifting. The subsequent
native conformal Dirichlet data and weak conormal use this same geometry.
This does not assert matching with the Euclidean singular half-end field.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
open Set Filter MeasureTheory UniformSpace PoincareMT Metric
open scoped Manifold ContDiff InnerProductSpace Topology
namespace Yamabe3.Analysis
open PoincareMT.LeviCivitaData.Dirichlet SpherePolar NativeChartSphereMetric
variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

structure NativeBoundaryGeometry (g : RiemannianMetric 3 M) (p : M) where
  e : OpenPartialHomeomorph E M
  gE : RiemannianMetric 3 E
  a : ℝ
  C : ℝ
  ha : 0 < a
  he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source
  hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target
  hs : closedBall (0 : E) (2 * a) ⊆ e.source
  center : e 0 = p
  hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v
  hcoeff : ∀ x ∈ closedBall (0 : E) (2 * a),
    gE.euclideanCoefficients x = g.pullbackCoefficients e x
  hC : 0 ≤ C
  hρ : ∀ θ : S, gE.pullbackVolumeDensity id (a • (θ : E)) ≤ C

/-- These are produced geometric data, not a new assumption on the metric. -/
theorem exists_nativeBoundaryGeometry (g : RiemannianMetric 3 M) (p : M) :
    Nonempty (NativeBoundaryGeometry g p) := by
  obtain ⟨e, r, gE, D, hr, hs, hep, he, hei, hcoeff, hGauss,
    hρSmooth, _, _, _, _, _, _⟩ := NormalCoordinates.exists_native_normalized_density g p
  have hrad : Continuous (fun θ : S => (r / 2) • (θ : E)) := by fun_prop
  have hc : Continuous (fun θ : S => gE.pullbackVolumeDensity id ((r / 2) • (θ : E))) :=
    hρSmooth.continuous.comp hrad
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨{
    e := e
    gE := gE
    a := r / 2
    C := max C 0
    ha := by positivity
    he := he
    hei := hei
    hs := ?_
    center := hep
    hGauss := hGauss
    hcoeff := ?_
    hC := le_max_right _ _
    hρ := ?_ }⟩
  · simpa only [show 2 * (r / 2) = r by ring] using hs
  · simpa only [show 2 * (r / 2) = r by ring] using hcoeff
  · intro θ
    have hb : |gE.pullbackVolumeDensity id ((r / 2) • (θ : E))| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC θ (mem_univ θ)
    exact (le_abs_self _).trans (hb.trans (le_max_left C 0))

namespace NativeBoundaryGeometry
variable {g : RiemannianMetric 3 M} {p : M} (G : NativeBoundaryGeometry g p)
def exterior : Set M := (G.e '' closedBall (0 : E) G.a)ᶜ

theorem annulus_source : sphereTraceAnnulus G.a (2 * G.a) ⊆ G.e.source := by
  intro x hx
  exact G.hs (by simpa only [mem_closedBall, dist_zero_right] using hx.2)

def trace := nativePhysicalSphereTraceCLM g G.gE G.e G.he G.hei G.ha
  (show G.a < 2 * G.a from by linarith only [G.ha])
  (show G.a ∈ Icc G.a (2 * G.a) from ⟨le_rfl, by linarith only [G.ha]⟩)
  G.annulus_source G.hC
  (fun θ => G.hcoeff _ (by
    rw [mem_closedBall, dist_zero_right, EuclideanSphereTrace.norm_sphereTrace_radial _ G.ha.le]
    linarith only [G.ha]))
  (fun θ => G.hGauss (G.a • (θ : E))) G.hρ

end NativeBoundaryGeometry

/-- Geometry is fixed before every source and H1 lifting. The same produced
data retain the prescribed source, physical value trace and conormal formula.
There is no free inverse, weak equation or gap hypothesis. -/
theorem exists_native_geometric_conformal_dirichlet_data
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (p : M) :
    ∃ G : NativeBoundaryGeometry g p,
      ∀ (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure),
        ∃ d : NativeWeakEllipticDataSpace g G.exterior g.leviCivitaData.scalarCurvature
          g.leviCivitaData.contMDiff_scalarCurvature,
          d.val.2 = F ∧ G.trace d.val.1 = G.trace ell ∧
          ∀ v : H1Zero g.leviCivitaData univ,
            nativeRestrictedEllipticForm g G.exterior g.leviCivitaData.scalarCurvature
              g.leviCivitaData.contMDiff_scalarCurvature d.val.1 v -
              (∫ x in G.exterior, F x * toL2 g.leviCivitaData univ v x ∂g.volumeMeasure) =
              EuclideanSphereTrace.nativeWeakPhysicalConormalCLM g G.gE G.e G.he G.hei
                G.hGauss G.ha G.hs G.hcoeff G.hC G.hρ g.leviCivitaData.scalarCurvature
                g.leviCivitaData.contMDiff_scalarCurvature d
                (HilbertTraceQuotient.quotientMap G.trace v) := by
  obtain ⟨G⟩ := exists_nativeBoundaryGeometry g p
  refine ⟨G, fun ell F => ?_⟩
  obtain ⟨d, hF, hT⟩ := exists_native_conformal_exterior_data g hY
    G.gE G.e G.he G.hei G.hGauss G.ha G.hs G.hcoeff G.hC G.hρ ell F
  refine ⟨d, hF, hT, fun v => ?_⟩
  have h := EuclideanSphereTrace.nativeWeakPhysicalConormal_quotientMap g G.gE G.e G.he G.hei
    G.hGauss G.ha G.hs G.hcoeff G.hC G.hρ g.leviCivitaData.scalarCurvature
    g.leviCivitaData.contMDiff_scalarCurvature d v
  simpa only [NativeBoundaryGeometry.exterior, NativeBoundaryGeometry.trace,
    nativeWeakEnergySourceDataCLM_apply, nativeRestrictedL2SourceOperator_apply,
    hF] using h.symm

end Yamabe3.Analysis
