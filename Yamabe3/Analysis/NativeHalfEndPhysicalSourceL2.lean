import Yamabe3.Analysis.NativeHalfEndSourceRegularity
import Yamabe3.Analysis.Cylinder.NativeHalfEndPhysicalForcing
import Yamabe3.Analysis.UniformElliptic.NativeL2SquareConvergence

/-! The original source value, not merely its high projection, supplies a
bounded physical L2 class on the punctured ball. The exact sign, factor
eight and physical volume are preserved. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
local notation "O" => ball (0:E) 1\{(0:E)}

theorem halfEndEuclideanPhysicalSource_memLp (f:HalfEndSourceValue) :
    MemLp (halfEndEuclideanPhysicalSource f) 2 (volume.restrict O) ∧
      (∫x in O,(halfEndEuclideanPhysicalSource f x)^2) ≤ 32*(‖nativeSphereL2Inclusion‖*‖f‖)^2 := by
  let z:=halfEndSourceCylinderCLM f
  let U:=cylinderToAngularL2CLM z
  have hbound(t:ℝ)(ht:0 ≤ t):‖U t‖ ≤ ‖nativeSphereL2Inclusion‖*‖f‖ :=
    (U.norm_coe_le_norm t).trans ((cylinderToAngularL2CLM_norm_le z).trans
      (mul_le_mul_of_nonneg_left (halfEndSourceCylinderCLM_norm_le f) (norm_nonneg nativeSphereL2Inclusion)))
  obtain ⟨hm,hb⟩:=native_halfEnd_physicalForcing_memLp U.continuous z.continuous.measurable
    (fun t=>(cylinderTestL2_ae z z.continuous t).symm) hbound
  have he:physicalForcing (fun p=>Real.exp (-2*p.1)*z p)=ᵐ[volume.restrict O] halfEndEuclideanPhysicalSource f := by
    filter_upwards [ae_restrict_mem (isOpen_ball.sdiff isClosed_singleton).measurableSet] with x hx
    have hxn:‖x‖<1:=by simpa only [mem_ball,dist_zero_right] using hx.1
    exact halfEndSourceCylinder_physicalForcing f hx.2 hxn.le
  refine ⟨hm.ae_eq he,?_⟩
  have hi:(∫x in O,(physicalForcing (fun p=>Real.exp (-2*p.1)*z p) x)^2)=
      ∫x in O,(halfEndEuclideanPhysicalSource f x)^2 := integral_congr_ae (he.mono fun x hx=>congrArg (fun t:ℝ=>t^2) hx)
  rwa [hi] at hb

def halfEndPhysicalSourceL2 (f:HalfEndSourceValue) : Lp ℝ 2 (volume.restrict O) :=
  (halfEndEuclideanPhysicalSource_memLp f).1.toLp (halfEndEuclideanPhysicalSource f)

theorem halfEndPhysicalSourceL2_ae (f:HalfEndSourceValue) :
    (halfEndPhysicalSourceL2 f:E→ℝ)=ᵐ[volume.restrict O] halfEndEuclideanPhysicalSource f :=
  (halfEndEuclideanPhysicalSource_memLp f).1.coeFn_toLp

def halfEndPhysicalSourceL2Linear : HalfEndSourceValue→ₗ[ℝ]Lp ℝ 2 (volume.restrict O) where
  toFun:=halfEndPhysicalSourceL2
  map_add' f h:=by
    apply Lp.ext
    filter_upwards [halfEndPhysicalSourceL2_ae (f+h),halfEndPhysicalSourceL2_ae f,
      halfEndPhysicalSourceL2_ae h,Lp.coeFn_add (halfEndPhysicalSourceL2 f) (halfEndPhysicalSourceL2 h)] with x hs hf hh ha
    rw [hs,ha]
    change halfEndEuclideanPhysicalSource (f+h) x=halfEndPhysicalSourceL2 f x+halfEndPhysicalSourceL2 h x
    rw [hf,hh]
    simp only [halfEndEuclideanPhysicalSource,halfEndSourceExtension_add,mul_add]
  map_smul' c f:=by
    apply Lp.ext
    filter_upwards [halfEndPhysicalSourceL2_ae (c • f),halfEndPhysicalSourceL2_ae f,
      Lp.coeFn_smul c (halfEndPhysicalSourceL2 f)] with x hs hf ha
    change halfEndPhysicalSourceL2 (c • f) x=(c • halfEndPhysicalSourceL2 f:Lp ℝ 2 (volume.restrict O)) x
    rw [hs,ha]
    change halfEndEuclideanPhysicalSource (c • f) x=c*halfEndPhysicalSourceL2 f x
    rw [hf]
    simp only [halfEndEuclideanPhysicalSource,halfEndSourceExtension_smul]
    ring

theorem halfEndPhysicalSourceL2_norm (f:HalfEndSourceValue) :
    ‖halfEndPhysicalSourceL2 f‖ ≤ (Real.sqrt 32*‖nativeSphereL2Inclusion‖)*‖f‖ := by
  have he:=native_norm_toLp_sq_eq_integral_sq (halfEndEuclideanPhysicalSource_memLp f).1
  change ‖halfEndPhysicalSourceL2 f‖^2=_ at he
  have hb:=he.le.trans (halfEndEuclideanPhysicalSource_memLp f).2
  have hs:(Real.sqrt 32*‖nativeSphereL2Inclusion‖*‖f‖)^2=32*(‖nativeSphereL2Inclusion‖*‖f‖)^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num)]
    ring
  have hp:0 ≤ Real.sqrt 32*‖nativeSphereL2Inclusion‖*‖f‖:=by positivity
  nlinarith [norm_nonneg (halfEndPhysicalSourceL2 f)]

def halfEndPhysicalSourceL2CLM : HalfEndSourceValue→L[ℝ]Lp ℝ 2 (volume.restrict O) :=
  halfEndPhysicalSourceL2Linear.mkContinuous (Real.sqrt 32*‖nativeSphereL2Inclusion‖) halfEndPhysicalSourceL2_norm

#print axioms halfEndEuclideanPhysicalSource_memLp
#print axioms halfEndPhysicalSourceL2_ae
#print axioms halfEndPhysicalSourceL2_norm
#print axioms halfEndPhysicalSourceL2CLM
end Yamabe3.Analysis.UniformElliptic
