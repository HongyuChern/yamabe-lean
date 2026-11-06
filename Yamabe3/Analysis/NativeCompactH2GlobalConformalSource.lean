import Yamabe3.Analysis.NativeGlobalH2ChartSourceCanonical
import Yamabe3.Analysis.NativeWeakOperatorZeroLocality

/-! A global H2 field supported in a retained compact ball constructs
its ACTUAL global L2 conformal source. Weak derivative locality proves
source support; no source-free equation is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal lp
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak

 theorem nativeGlobalConformalDensity_zero_on_open
    (g:RiemannianMetric 3 E) {u:E→ℝ} (hu:MemWkp 2 2 u univ)
    {O:Set E} (hO:IsOpen O) (hz:EqOn u (fun _=>0) O):
    nativeWeakConformalDensity univ g u=ᵐ[volume.restrict O](fun _=>0):=by
  filter_upwards [nativeGlobalWeakJacobian_zero_on_open hu hO hz g 1 (fun _=>0) 0,
    ae_restrict_mem hO.measurableSet] with x hx hxO
  rw [nativeWeakJacobian_one_conformal_density univ g (fun _=>0) 0 u x,hx,hz hxO]
  ring

 theorem exists_nativeCompactH2_global_conformal_source
    (g:RiemannianMetric 3 E) {u:E→ℝ} (hu:MemWkp 2 2 u univ)
    {r R:ℝ} (hr:r<R) (hz:∀x:E,x∉closedBall (0:E) r→u x=0):
    ∃F:Lp ℝ 2 (volume:Measure E),(F:E→ℝ)=ᵐ[volume]nativeWeakConformalDensity univ g u ∧
      nativeWeakConformalDensity univ g u=ᵐ[volume.restrict (closedBall (0:E) r)ᶜ](fun _=>0):=by
  let K:=closedBall (0:E) R
  let B:=ball (0:E) (R+1)
  have hKB:K⊆B:=by
    intro x hx
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx) (by linarith))
  have hBc:IsCompact (closure B):=Metric.isCompact_of_isClosed_isBounded isClosed_closure
    ((Metric.isBounded_ball (x:=(0:E)) (r:=R+1)).closure)
  have huB:MemWkp 2 2 u B:=hu.mono_set (by norm_num) isOpen_ball (subset_univ _)
  have hRaw:MemLp (K.indicator (nativeWeakConformalDensity B g u)) 2 (volume:Measure E):=by
    apply (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
    exact (nativeWeakConformalDensity_memLp isOpen_ball hBc g huB).mono_measure (Measure.restrict_mono hKB le_rfl)
  let F:=hRaw.toLp (K.indicator (nativeWeakConformalDensity B g u))
  have hF:(F:E→ℝ)=ᵐ[volume](K.indicator (nativeWeakConformalDensity B g u)):=hRaw.coeFn_toLp
  have hzero:=nativeGlobalConformalDensity_zero_on_open g hu isClosed_closedBall.isOpen_compl (fun x hx=>hz x hx)
  have hzGlobal:∀ᵐx:E∂volume,x∉closedBall (0:E) r→nativeWeakConformalDensity univ g u x=0:=
    (ae_restrict_iff' measurableSet_closedBall.compl).mp hzero
  have hm:=nativeWeakConformalDensity_mono (D:=B) isOpen_ball (subset_univ _) hu g
  have hmK:=ae_mono (Measure.restrict_mono hKB le_rfl) hm
  have hmGlobal:=(ae_restrict_iff' measurableSet_closedBall).mp hmK
  refine ⟨F,?_,hzero⟩
  filter_upwards [hF,hzGlobal,hmGlobal] with x hf hz hm
  by_cases hx:x∈K
  · rw [hf,indicator_of_mem hx]
    exact (hm hx).symm
  · rw [hf,indicator_of_notMem hx]
    exact (hz (fun h=>hx ((closedBall_subset_closedBall hr.le) h))).symm

#print axioms nativeGlobalConformalDensity_zero_on_open
#print axioms exists_nativeCompactH2_global_conformal_source
end Yamabe3.Analysis.SpherePolar
