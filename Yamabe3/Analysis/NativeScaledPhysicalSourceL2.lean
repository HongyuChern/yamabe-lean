import Yamabe3.Analysis.NativeHalfEndPhysicalSourceL2
import Yamabe3.Analysis.NativeH4InteriorL2Data

/-! The original full half-end physical source becomes a genuine native
L2 source at the same radius and metric density. The factor eight is
already retained in halfEndEuclideanPhysicalSource; it is not divided
out a second time. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis
open SpherePolar UniformElliptic NativeChartSphereMetric
open PoincareMT.LeviCivitaData.Dirichlet
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Ωunit" => ball (0:E) 1\{(0:E)}

def zeroHalfEndPhysicalSource (f:HalfEndSourceValue) : E→ℝ := (Ωunit).indicator (halfEndEuclideanPhysicalSource f)

theorem zeroHalfEndPhysicalSource_measurable (f:HalfEndSourceValue) :
    Measurable (zeroHalfEndPhysicalSource f) := by
  convert (continuousOn_halfEndEuclideanPhysicalSource f).measurable_piecewise (continuous_const (y:=(0:ℝ))).continuousOn
    (isOpen_ball.sdiff isClosed_singleton).measurableSet using 1
  funext x
  by_cases hx:x∈Ωunit <;> simp [zeroHalfEndPhysicalSource,Set.piecewise,hx]

theorem zeroHalfEndPhysicalSource_memLp (f:HalfEndSourceValue) :
    MemLp (zeroHalfEndPhysicalSource f) 2 volume :=
  (memLp_indicator_iff_restrict (isOpen_ball.sdiff isClosed_singleton).measurableSet).mpr
    (halfEndEuclideanPhysicalSource_memLp f).1

def nativeScaledPhysicalSource (gE:RiemannianMetric 3 E) (a:ℝ) (f:HalfEndSourceValue) (x:E) :ℝ :=
  zeroHalfEndPhysicalSource f (a⁻¹ • x)/(a^2*gE.pullbackVolumeDensity id x)

private theorem inverse_density_continuous (gE:RiemannianMetric 3 E) {a:ℝ} (ha:0<a) :
    Continuous (fun x:E=>(a^2*gE.pullbackVolumeDensity id x)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp:=gE.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x) contMDiffAt_id (by simpa using Function.injective_id)
  exact (continuousAt_const.mul hp.1.continuousAt).inv₀ (mul_ne_zero (pow_ne_zero _ ha.ne') hp.2.ne')

theorem nativeScaledPhysicalSource_measurable (gE:RiemannianMetric 3 E) {a:ℝ} (ha:0<a) (f:HalfEndSourceValue) :
    Measurable (nativeScaledPhysicalSource gE a f) := by
  exact ((zeroHalfEndPhysicalSource_measurable f).comp (continuous_id.const_smul a⁻¹).measurable).mul
    (inverse_density_continuous gE ha).measurable

theorem nativeScaledPhysicalSource_memLp (gE:RiemannianMetric 3 E) {a:ℝ} (ha:0<a) (f:HalfEndSourceValue)
    {K:Set E} (hK:IsCompact K) : MemLp (nativeScaledPhysicalSource gE a f) 2 (volume.restrict K) := by
  have hf:MemLp (fun x:E=>zeroHalfEndPhysicalSource f (a⁻¹ • x)) 2 volume:=by
    have hh:=memLp_comp_dilation (r:=a⁻¹) (inv_ne_zero ha.ne')
      (O:=(univ:Set E)) (by simpa only [Measure.restrict_univ] using zeroHalfEndPhysicalSource_memLp f)
    simpa only [preimage_univ,Measure.restrict_univ] using hh
  have hi:MemLp (fun x:E=>(a^2*gE.pullbackVolumeDensity id x)⁻¹*zeroHalfEndPhysicalSource f (a⁻¹ • x)) 2 (volume.restrict K):=
    (hf.restrict K).mul' (continuousOn_compact_memLp_top hK (inverse_density_continuous gE ha).continuousOn)
  apply hi.ae_eq
  exact Eventually.of_forall fun x=>by dsimp [nativeScaledPhysicalSource];ring

theorem nativeScaledPhysicalSource_of_mem (gE:RiemannianMetric 3 E) {a:ℝ} (ha:0<a) (f:HalfEndSourceValue)
    {x:E} (hx:x∈ball (0:E) a\{0}) :
    nativeScaledPhysicalSource gE a f x=
      halfEndEuclideanPhysicalSource f (a⁻¹ • x)/(a^2*gE.pullbackVolumeDensity id x) := by
  have hn:‖x‖<a:=by simpa only [mem_ball,dist_zero_right] using hx.1
  have hy:a⁻¹ • x∈Ωunit:=by
    constructor
    · rw [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le]
      calc a⁻¹*‖x‖ < a⁻¹*a := mul_lt_mul_of_pos_left hn (inv_pos.mpr ha)
           _ = 1 := inv_mul_cancel₀ ha.ne'
    · exact smul_ne_zero (inv_ne_zero ha.ne') hx.2
  simp only [nativeScaledPhysicalSource,zeroHalfEndPhysicalSource,indicator_of_mem hy]

variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

def nativeOriginalPhysicalSourceL2
    (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q) (f:HalfEndSourceValue) : Lp ℝ 2 g.volumeMeasure :=
  nativeCompactChartSource g G.e G.he G.hei (isCompact_closedBall _ _) (nativeBoundaryBallSource g G)
    (nativeScaledPhysicalSource_measurable G.gE G.ha f)
    (nativeScaledPhysicalSource_memLp G.gE G.ha f (isCompact_closedBall _ _))

theorem nativeOriginalPhysicalSourceL2_ae
    (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q) (f:HalfEndSourceValue) :
    (nativeOriginalPhysicalSourceL2 g G f:M→ℝ)=ᵐ[g.volumeMeasure]
      nativeCompactChartFunction G.e (closedBall (0:E) G.a) (nativeScaledPhysicalSource G.gE G.a f) :=
  nativeCompactChartSource_ae _ _ _ _ _ _ _ _

#print axioms zeroHalfEndPhysicalSource_measurable
#print axioms zeroHalfEndPhysicalSource_memLp
#print axioms nativeScaledPhysicalSource_memLp
#print axioms nativeScaledPhysicalSource_of_mem
#print axioms nativeOriginalPhysicalSourceL2_ae
end Yamabe3.Analysis
