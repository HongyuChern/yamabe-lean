import Yamabe3.Analysis.NativeWeakOperatorZeroLocality
import Yamabe3.Analysis.OffZeroCompactL2

/-! Actual integrability justifying the full-operator/potential split
on compact exterior tests. No global boundedness of the inverse-square
potential or general singular H1 bilinear form is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix Delaunay
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak

 theorem nativeWeakZeroJacobian_memLp_precompact
    {O:Set E} (hO:IsOpen O) (hOc:IsCompact (closure O)) (g:RiemannianMetric 3 E) (a:ℝ)
    {u:E→ℝ} (hu:MemWkp 2 2 u O):
    MemLp (nativeWeakRescaledDelaunayJacobian O g a (fun _=>0) 0 u) 2 (volume.restrict O):=by
  have hA(i j:Fin 3):ContDiff ℝ ∞ (fun x:E=>nativeScaledDivergenceMatrix g a x i j):=
    (contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul a)
  obtain ⟨C,hC,hD⟩:=exists_weakDivergenceSource_bound hO hOc (nativeScaledDivergenceMatrix g a) hA
  let q:E→ℝ:=fun x=>a^2*nativePotentialDensity g (a • x)
  have hq:Continuous q:=continuous_const.mul ((contDiff_nativePotentialDensity g).continuous.comp (continuous_const_smul a))
  have hqm:MemLp q ⊤ (volume.restrict O):=(continuousOn_compact_memLp_top hOc hq.continuousOn).mono_measure
    (Measure.restrict_mono subset_closure le_rfl)
  apply ((hD u hu).1.memLp.add (hu.memLp.mul' hqm)).ae_eq
  exact Eventually.of_forall fun x=>by
    rw [nativeWeakJacobian_eq_divergence]
    simp only [Pi.add_apply,nativeDelaunayPotentialError,annularDelaunayPotential,
      zero_pow (by decide:(4:ℕ)≠0),mul_zero,zero_div,zero_add,add_zero]
    dsimp only [q]

 theorem nativeGlobalWeakZeroJacobian_test_integrable
    (g:RiemannianMetric 3 E) (a:ℝ) {u:E→ℝ} (hu:MemWkp 2 2 u univ)
    (φ:E→ℝ) (hφ:Continuous φ) (hc:HasCompactSupport φ):
    Integrable (fun x:E=>nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x*φ x):=by
  obtain ⟨R,hR⟩:=hc.isCompact.isBounded.subset_ball (0:E)
  let B:=ball (0:E) R
  have hBc:IsCompact (closure B):=Metric.isCompact_of_isClosed_isBounded isClosed_closure
    ((Metric.isBounded_ball (x:=(0:E)) (r:=R)).closure)
  have huB:MemWkp 2 2 u B:=hu.mono_set (by norm_num) isOpen_ball (subset_univ _)
  have hm:=nativeWeakZeroJacobian_memLp_precompact isOpen_ball hBc g a huB
  have hφm:MemLp φ 2 (volume:Measure E):=hφ.memLp_of_hasCompactSupport hc
  have hi:Integrable (B.indicator (fun x:E=>nativeWeakRescaledDelaunayJacobian B g a (fun _=>0) 0 u x*φ x)):=
    (integrable_indicator_iff measurableSet_ball).mpr (hm.integrable_mul (hφm.restrict B))
  have hj:=nativeWeakRescaledDelaunayJacobian_mono (D:=B) isOpen_ball (subset_univ _) hu g a (fun _=>0) 0
  have hh:=(ae_restrict_iff' measurableSet_ball).mp hj
  apply hi.congr
  filter_upwards [hh] with x hx
  by_cases hxB:x∈B
  · rw [indicator_of_mem hxB]
    exact congrArg (fun r:ℝ=>r*φ x) (hx hxB).symm
  · rw [indicator_of_notMem hxB,image_eq_zero_of_notMem_tsupport (fun ht=>hxB (hR ht)),mul_zero]

 theorem nativeGlobalPotential_test_integrable
    (g:RiemannianMetric 3 E) (a:ℝ) (V:ℝ→ᵇℝ) {u:E→ℝ} (hu:MemLp u 2 (volume:Measure E))
    (φ:E→ℝ) (hφ:Continuous φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ):
    Integrable (fun x:E=>g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x*φ x):=by
  let ψ:E→ℝ:=fun x=>g.pullbackVolumeDensity id (a • x)*φ x
  have hψ:Continuous ψ:=((native_density_smooth_positive g).1.continuous.comp (continuous_const_smul a)).mul hφ
  have hψc:HasCompactSupport ψ:=hc.mul_left
  have hψ0:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
  have hm:=nativeHalfEndPotentialCoefficient_mul_test_memLp V hψ hψc hψ0
  apply (hu.integrable_mul hm).congr
  exact Eventually.of_forall fun x=>by dsimp only [ψ,Pi.mul_apply];ring

 theorem nativeGlobalFullBCF_test_split
    (g:RiemannianMetric 3 E) (a:ℝ) (V:ℝ→ᵇℝ) {u:E→ℝ} (hu:MemWkp 2 2 u univ)
    (φ:E→ℝ) (hφ:Continuous φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ):
    (∫x:E,(nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x-
      g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x)*φ x)=
      (∫x:E,nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x*φ x)-
      (∫x:E,g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x*φ x):=by
  have hm:MemLp u 2 (volume:Measure E):=by simpa only [Measure.restrict_univ] using hu.memLp
  calc
    _=(∫x:E,nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x*φ x-
      g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x*φ x):=by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x=>sub_mul _ _ _)
    _=_:=integral_sub (nativeGlobalWeakZeroJacobian_test_integrable g a hu φ hφ hc)
      (nativeGlobalPotential_test_integrable g a V hm φ hφ hc h0)

#print axioms nativeWeakZeroJacobian_memLp_precompact
#print axioms nativeGlobalWeakZeroJacobian_test_integrable
#print axioms nativeGlobalPotential_test_integrable
#print axioms nativeGlobalFullBCF_test_split
end Yamabe3.Analysis.SpherePolar
