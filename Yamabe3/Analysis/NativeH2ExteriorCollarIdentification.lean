import Yamabe3.Analysis.NativeH2ChartSourceIdentification
import Yamabe3.Analysis.NativeBCFWeakPhysicalRow
import Yamabe3.Analysis.NativeWeakPhysicalConformalScaling
import Yamabe3.Analysis.NativeGlobalH2ConformalScaling

/-! Identify the actual exterior collar operator from the SAME completed
field's native equation and volume representative. No sphere-a.e. restriction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix Delaunay PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeH2_exterior_collar_identification
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (hcoeff:∀x∈K,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {a:ℝ} (ha:0<a)
    (hDc:IsCompact (closure (euclideanDilatedDomain a nativeNegativeEntranceCollar)))
    (hDK:closure (euclideanDilatedDomain a nativeNegativeEntranceCollar)⊆K)
    (V:ℝ→ᵇℝ) (J:nativeCollarJetClosure)
    (W:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (hrep:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict
      (e '' euclideanDilatedDomain a nativeNegativeEntranceCollar)]
      coordinateExtension e (fun x:E=>(J.val.1:E→ℝ) (a⁻¹ • x)))
    (hF:(W,F)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const
      (e '' euclideanDilatedDomain a nativeNegativeEntranceCollar))
    (hFcoord:(fun x:E=>F (e (a • x)))=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x=>8*(a⁻¹)^2*nativeHalfEndPotentialCoefficient V x*(J.val.1:E→ℝ) x)):
    (nativeExteriorNativeJacobianCLM gE a V J.val:E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar](fun _=>0):=by
  let D:=euclideanDilatedDomain a nativeNegativeEntranceCollar
  let U:E→ℝ:=fun x=>(J.val.1:E→ℝ) (a⁻¹ • x)
  have hD:IsOpen D:=nativeNegativeEntranceCollar_open.preimage (continuous_const_smul a⁻¹)
  have hDs:D⊆e.source:=(subset_closure.trans hDK).trans hKs
  have hΩ:IsOpen (e '' D):=e.isOpen_image_of_subset_source hD hDs
  have hrep':(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' D)]
      nativeCompactChartFunction e (closure D) U:=by
    filter_upwards [hrep,ae_restrict_mem hΩ.measurableSet] with y hy hyD
    obtain ⟨x,hx,rfl⟩:=hyD
    rw [hy,nativeCompactChartFunction,coordinateExtension_comp_apply e _ (hDs hx),
      coordinateExtension_comp_apply e _ (hDs hx),indicator_of_mem (subset_closure hx)]
  have hJ:MemWkp 2 2 (J.val.1:E→ℝ) nativeNegativeEntranceCollar:=
    (nativeCollarJetClosure_memH2 J).mono_set (by norm_num) nativeNegativeEntranceCollar_open inter_subset_left
  have hu:MemWkp 2 2 U D:=memWkp_comp_dilation (inv_ne_zero ha.ne') nativeNegativeEntranceCollar_open
    (by norm_num) 2 hJ
  have hden:=nativeH2_chart_source_identification g gE e he hei hK hKs hcoeff hD hDc hDK U
    ((Lp.stronglyMeasurable J.val.1).measurable.comp (continuous_const_smul a⁻¹).measurable) hu W F hrep' hF
  have heq:nativeWeakRescaledDelaunayJacobian nativeNegativeEntranceCollar gE a (fun _=>0) 0 J.val.1
      =ᵐ[volume.restrict nativeNegativeEntranceCollar]
        (fun x=>(8*nativeWeakRescaledDelaunayJacobian nativeNegativeEntranceCollar gE a (fun _=>0) 0 J.val.1 x)/8):=
    Eventually.of_forall (fun _=>by ring)
  have h0:nativeNegativeEntranceCollar⊆({0}ᶜ:Set E):=fun _ hx=>hx.1.1
  have hs:=(nativeWeak_physical_conformal_source gE (fun _=>0) 0 ha nativeNegativeEntranceCollar_open h0 hJ heq).2
  have hd:=ae_comp_dilation ha.ne' hden
  have hsd:=ae_comp_dilation ha.ne' hs
  simp only [D,euclideanDilatedDomain,preimage_preimage,Function.comp_def,smul_smul,
    inv_mul_cancel₀ ha.ne',one_smul] at hd hsd
  have hmono:=nativeWeakRescaledDelaunayJacobian_mono nativeNegativeEntranceCollar_open
    inter_subset_left (nativeCollarJetClosure_memH2 J) gE a (fun _=>0) 0
  filter_upwards [nativeExteriorNativeJacobian_weak_ae gE a V J,hmono,hd,hsd,hFcoord] with x hx hm hd hs hf
  simp only [U,smul_smul,inv_mul_cancel₀ ha.ne',one_smul,annularDelaunayPotential,
    zero_pow (by decide:(4:ℕ)≠0),mul_zero,zero_mul,zero_div,sub_zero] at hs
  have hJac:nativeWeakRescaledDelaunayJacobian nativePoissonEntranceCollar gE a (fun _=>0) 0 J.val.1 x=
      gE.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*(J.val.1:E→ℝ) x:=by
    rw [hf] at hd
    rw [hs] at hd
    rw [hm]
    have hcancel:(a⁻¹)^2≠0:=pow_ne_zero _ (inv_ne_zero ha.ne')
    apply (mul_left_cancel₀ hcancel)
    linear_combination hd/8
  rw [hx]
  simp only [nativeWeakRescaledDelaunayJacobian,nativeDelaunayPotentialError,annularDelaunayPotential,
    zero_pow (by decide:(4:ℕ)≠0),mul_zero,zero_mul,zero_div,sub_zero] at hJac
  linear_combination 8*hJac

#print axioms nativeH2_exterior_collar_identification
end Yamabe3.Analysis.SpherePolar
