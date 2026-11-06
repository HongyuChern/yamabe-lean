import Yamabe3.Analysis.NativeWeakPhysicalConformalScaling
import Yamabe3.Analysis.NativeWeakJacobianLocality

/-! Genuine global H2 physical scaling of the native conformal weak
operator, including the three-dimensional volume factor. The puncture
is removed only as a volume null set after proving the local identity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix Delaunay
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak

 theorem nativeWeakConformalDensity_mono
    {O D:Set E} (hD:IsOpen D) (hDO:D⊆O) {u:E→ℝ} (hu:MemWkp 2 2 u O)
    (g:RiemannianMetric 3 E):
    nativeWeakConformalDensity O g u=ᵐ[volume.restrict D]nativeWeakConformalDensity D g u:=by
  have hh:=nativeWeakRescaledDelaunayJacobian_mono hD hDO hu g 1 (fun _=>0) 0
  filter_upwards [hh] with x hx
  rw [nativeWeakJacobian_one_conformal_density O g (fun _=>0) 0 u x,
    nativeWeakJacobian_one_conformal_density D g (fun _=>0) 0 u x,hx]

 theorem nativeGlobalH2_physical_conformal_density
    (g:RiemannianMetric 3 E) {a:ℝ} (ha:0<a) {u:E→ℝ} (hu:MemWkp 2 2 u univ):
    nativeWeakConformalDensity univ g (fun y:E=>u (a⁻¹ • y))=ᵐ[volume]
      (fun y=>8*(a⁻¹)^2*nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u (a⁻¹ • y)):=by
  let O:Set E:=({0}ᶜ:Set E)
  have hO:IsOpen O:=isClosed_singleton.isOpen_compl
  have huO:MemWkp 2 2 u O:=hu.mono_set (by norm_num) hO (subset_univ _)
  have he:nativeWeakRescaledDelaunayJacobian O g a (fun _=>0) 0 u=ᵐ[volume.restrict O]
      (fun x=>(8*nativeWeakRescaledDelaunayJacobian O g a (fun _=>0) 0 u x)/8):=
    Eventually.of_forall (fun x=>by ring)
  have hs:=nativeWeak_physical_conformal_source g (fun _=>0) 0 ha hO (Subset.refl O) huO he
  dsimp only at hs
  have hU:MemWkp 2 2 (fun y:E=>u (a⁻¹ • y)) univ:=by
    simpa only [preimage_univ] using memWkp_comp_dilation (inv_ne_zero ha.ne') isOpen_univ
      (by norm_num:(1:ℝ≥0∞)≤2) 2 hu
  have hD:euclideanDilatedDomain a O=O:=by
    ext x
    change (a⁻¹ • x≠0)↔x≠0
    rw [smul_ne_zero_iff]
    exact ⟨fun h=>h.2,fun h=>⟨inv_ne_zero ha.ne',h⟩⟩
  have hmono:=nativeWeakConformalDensity_mono hO (subset_univ _) hU g
  have hmonoU:=nativeWeakRescaledDelaunayJacobian_mono hO (subset_univ _) hu g a (fun _=>0) 0
  have hd:=ae_comp_dilation (inv_ne_zero ha.ne') hmonoU
  change (fun x=>nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u (a⁻¹ • x))=ᵐ[volume.restrict (euclideanDilatedDomain a O)]
    (fun x=>nativeWeakRescaledDelaunayJacobian O g a (fun _=>0) 0 u (a⁻¹ • x)) at hd
  rw [hD] at hd hs
  have hlocal:nativeWeakConformalDensity univ g (fun y:E=>u (a⁻¹ • y))=ᵐ[volume.restrict O]
      (fun y=>8*(a⁻¹)^2*nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u (a⁻¹ • y)):=by
    filter_upwards [hmono,hs.2,hd] with y hm hs hd
    rw [hm,hs,←hd]
    simp only [annularDelaunayPotential,zero_pow (by decide:(4:ℕ)≠0),mul_zero,zero_div,sub_zero]
    ring
  have hglobal:∀ᵐy:E∂volume,y∈O→nativeWeakConformalDensity univ g (fun z:E=>u (a⁻¹ • z)) y=
      8*(a⁻¹)^2*nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u (a⁻¹ • y):=
    (ae_restrict_iff' hO.measurableSet).mp hlocal
  filter_upwards [hglobal,volume.ae_ne (0:E)] with y hy hy0
  exact hy hy0

 theorem nativeGlobalH2_physical_conformal_pairing
    (g:RiemannianMetric 3 E) {a:ℝ} (ha:0<a) {u:E→ℝ} (hu:MemWkp 2 2 u univ) (φ:E→ℝ):
    (∫y:E,nativeWeakConformalDensity univ g (fun z:E=>u (a⁻¹ • z)) y*φ (a⁻¹ • y))=
      8*a*(∫x:E,nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x*φ x):=by
  have hs:=nativeGlobalH2_physical_conformal_density g ha hu
  calc
    _=(∫y:E,(8*(a⁻¹)^2)*(nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u (a⁻¹ • y)*φ (a⁻¹ • y))):=by
      apply integral_congr_ae
      filter_upwards [hs] with y hy
      rw [hy]
      ring
    _=(8*(a⁻¹)^2)*(a^3*(∫x:E,nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x*φ x)):=by
      rw [integral_const_mul]
      have hd:=setIntegral_comp_dilation (inv_ne_zero ha.ne') (univ:Set E)
        (fun x:E=>nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x*φ x)
      simp only [preimage_univ,Measure.restrict_univ,finrank_euclideanSpace_fin,inv_pow,inv_inv,
        abs_of_nonneg (pow_nonneg ha.le 3)] at hd
      rw [hd]
    _=_:=by field_simp [ha.ne'] <;> ring

#print axioms nativeWeakConformalDensity_mono
#print axioms nativeGlobalH2_physical_conformal_density
#print axioms nativeGlobalH2_physical_conformal_pairing
end Yamabe3.Analysis.SpherePolar
