import Yamabe3.Analysis.NativeCompactChartSource
import Yamabe3.Analysis.NativeScaledH4LocalL2
import Yamabe3.Analysis.NativeH4CompletedInteriorGreen
import Yamabe3.Analysis.NativeC2PointwiseEquation

/-! Genuine native-volume Laplacian class and induced-area radial flux
of the same scaled H4 field. These bounded classes support completion
extension of the already proved smooth-test Green identity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold RealInnerProductSpace
namespace Yamabe3.Analysis
open SpherePolar UniformElliptic NativeChartSphereMetric GreenParametrix
open PoincareMT.LeviCivitaData.Dirichlet
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "S" => SpherePolar.S
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem measurable_nativeOffZero_laplacian (gE:RiemannianMetric 3 E) (u:nativeC2OffZero) :
    Measurable (gE.leviCivitaData.laplacian u.val) :=
  (continuousOn_native_laplacian_C2 gE isClosed_singleton.isOpen_compl u.property).measurable_of_countable_compl
    (by simpa only [compl_compl] using countable_singleton (0:E))

theorem nativeBoundaryBallSource (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q) :
    closedBall (0:E) G.a⊆G.e.source :=
  (closedBall_subset_closedBall (by linarith only [G.ha])).trans G.hs

def nativeH4InteriorLaplacianL2
    (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    Lp ℝ 2 g.volumeMeasure :=
  nativeCompactChartSource g G.e G.he G.hei (isCompact_closedBall _ _) (nativeBoundaryBallSource g G)
    (measurable_nativeOffZero_laplacian G.gE (nativeScaledOffZero G.ha u))
    (nativeScaledH4_laplacian_memLp G.gE G.ha v u h0 hu (isCompact_closedBall _ _))

theorem nativeH4InteriorLaplacianL2_ae
    (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    (nativeH4InteriorLaplacianL2 g G v u h0 hu:M→ℝ)=ᵐ[g.volumeMeasure]
      nativeCompactChartFunction G.e (closedBall (0:E) G.a)
        (G.gE.leviCivitaData.laplacian (nativeScaledOffZero G.ha u).val) := nativeCompactChartSource_ae _ _ _ _ _ _ _ _

theorem nativeH4InteriorLaplacianL2_pairing_test
    (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    (φ:EnergyTest g.leviCivitaData univ) :
    inner ℝ (nativeH4InteriorLaplacianL2 g G v u h0 hu) (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ))=
      ∫x in closedBall (0:E) G.a,φ (G.e x)*G.gE.leviCivitaData.laplacian (nativeScaledOffZero G.ha u).val x ∂G.gE.volumeMeasure := by
  rw [nativeH4InteriorLaplacianL2,nativeCompactChartSource_pairing_test]
  rw [←integral_indicator (μ:=G.gE.volumeMeasure) measurableSet_closedBall,native_integral_eq_density G.gE,←integral_indicator (μ:=volume) measurableSet_closedBall]
  apply integral_congr_ae
  exact Eventually.of_forall fun x=>by
    by_cases hx:x∈closedBall (0:E) G.a
    · simp only [indicator_of_mem hx]
      rw [pullbackVolumeDensity_eq_of_coefficients g G.gE G.e x (G.hcoeff x
        ((closedBall_subset_closedBall (by linarith only [G.ha])) hx))]
      ring
    · simp only [indicator_of_notMem hx,zero_mul]

def nativeBoundaryArea (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q) : Measure S :=
  (chartRadiusMetric g G.e G.he G.hei G.a G.ha.ne' (nativeBoundarySphereSource g G)).volumeMeasure

theorem nativeH4InteriorFlux_memLp
    (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    MemLp (fun θ:S=>fderiv ℝ (nativeScaledOffZero G.ha u).val (G.a • (θ:E)) (θ:E)) 2 (nativeBoundaryArea g G) := by
  have hc:Continuous (fun θ:S=>fderiv ℝ (nativeScaledOffZero G.ha u).val (G.a • (θ:E)) (θ:E)):=
    (((nativeScaledH4_C1 G.ha v u h0 hu).continuous_fderiv (by norm_num)).comp
      (continuous_subtype_val.const_smul G.a)).clm_apply continuous_subtype_val
  letI:IsFiniteMeasureOnCompacts (nativeBoundaryArea g G):=by unfold nativeBoundaryArea;infer_instance
  exact hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def nativeH4InteriorFluxL2
    (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    Lp ℝ 2 (nativeBoundaryArea g G) := (nativeH4InteriorFlux_memLp g G v u h0 hu).toLp _

theorem nativeH4InteriorFluxL2_ae
    (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    (nativeH4InteriorFluxL2 g G v u h0 hu:S→ℝ)=ᵐ[nativeBoundaryArea g G]
      (fun θ:S=>fderiv ℝ (nativeScaledOffZero G.ha u).val (G.a • (θ:E)) (θ:E)) := MemLp.coeFn_toLp _

theorem nativeBoundary_trace_test_ae
    (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q)
    (φ:EnergyTest g.leviCivitaData univ) :
    (G.trace (φ:H1Zero g.leviCivitaData univ):S→ℝ)=ᵐ[nativeBoundaryArea g G] (fun θ:S=>φ (G.e (G.a • (θ:E)))) := by
  exact nativePhysicalSphereTraceCLM_coe_ae _ _ _ _ _ _ _ _ _ _ _ _ _ _

#print axioms nativeH4InteriorLaplacianL2_ae
#print axioms nativeH4InteriorLaplacianL2_pairing_test
#print axioms nativeH4InteriorFlux_memLp
#print axioms nativeH4InteriorFluxL2_ae
#print axioms nativeBoundary_trace_test_ae
end Yamabe3.Analysis
