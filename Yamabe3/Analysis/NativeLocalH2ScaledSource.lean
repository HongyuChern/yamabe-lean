import Yamabe3.Analysis.NativeOuterRepresentativeSourceL2
import Yamabe3.Analysis.SobolevLocalCompactExtension
import Yamabe3.Analysis.NativeSupportedOuterDecayField

/-! Fixed-scale L2 cutoff sources for every genuine representative of
one outer curve. Only local H2 away from zero is required; no extra far
threshold or unrecorded regularity witness is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem nativeBasicAnnulus_precompact_off_zero:
    IsCompact (closure halfEndBasicAnnulus) ∧ closure halfEndBasicAnnulus⊆({0}ᶜ:Set E):=by
  constructor
  · apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
    apply Bornology.IsBounded.closure
    exact (Metric.isBounded_ball (x:=(0:E)) (r:=2)).subset (fun x hx=>by simpa using hx.2)
  · have hcl:closure halfEndBasicAnnulus⊆{x:E|(1/2:ℝ)≤‖x‖}:=
      closure_minimal (fun x hx=>hx.1.le) (isClosed_le continuous_const continuous_norm)
    intro x hx h0
    have hh:=hcl hx
    change x=0 at h0
    change (1/2:ℝ)≤‖x‖ at hh
    rw [h0,norm_zero] at hh
    norm_num at hh

theorem nativeLocalH2_weighted_basicAnnulus {u:E→ℝ}
    (hu:MemWkpLocally 2 u ({0}ᶜ:Set E)) (s:ℝ):
    MemWkp 2 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus:=by
  let r:=Real.exp (-s)
  let K:=(fun x:E=>r • x) '' closure halfEndBasicAnnulus
  have hK:IsCompact K:=nativeBasicAnnulus_precompact_off_zero.1.image (continuous_const_smul r)
  have hK0:K⊆({0}ᶜ:Set E):=by
    rintro y ⟨x,hx,rfl⟩ hz
    exact nativeBasicAnnulus_precompact_off_zero.2 hx ((smul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero (-s)))
  obtain ⟨v,U,hU,hKU,hvc,hv,he⟩:=exists_compact_sobolev_extension_near_compact hu hK hK0
  have hd:=memWkp_comp_dilation (Real.exp_ne_zero (-s)) isOpen_univ (by norm_num:(1:ℝ≥0∞)≤2) 2 hv
  simp only [preimage_univ] at hd
  have hm:MemWkp 2 2 (weightedPhysicalDilation s v) halfEndBasicAnnulus:=by
    exact (MemWkp.const_smul (by norm_num) isOpen_univ hd (Real.exp (3*s/2))).mono_set
      (by norm_num) halfEndBasicAnnulus_isOpen (subset_univ _)
  apply (MemWkp_congr_ae (by norm_num) halfEndBasicAnnulus_isOpen ?_).mp hm
  filter_upwards [ae_restrict_mem halfEndBasicAnnulus_isOpen.measurableSet] with x hx
  exact congrArg (fun q:ℝ=>Real.exp (3*s/2)*q)
    (he (hKU ⟨x,subset_closure hx,rfl⟩))

theorem nativeOuter_same_curve_local_H2
    (b:ℝ) {τ:ℝ} (ht:0<τ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
    (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ))
    {w:ℝ×S→ℝ} (hw:Measurable w)
    (hwcurve:∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t:S→ℝ)):
    MemWkpLocally 2 (cylinderLift w) ({0}ᶜ:Set E):=by
  obtain ⟨z,hz,hl,hzcurve,hzjet⟩:=exists_nativeSupportedOuter_same_curve_all_scale b ht F d n σ hσ
  have he:=native_lift_ae_eq_of_joint_slices hz hw (fun t=>(hzcurve t).trans (hwcurve t).symm)
  intro x hx
  obtain ⟨U,hU,hxU,hU0,hm⟩:=hl x hx
  exact ⟨U,hU,hxU,hU0,(MemWkp_congr_ae (by norm_num) hU (ae_restrict_of_ae he)).mp hm⟩

theorem nativeOuter_same_curve_cutoff_source_L2
    (b:ℝ) {τ:ℝ} (ht:0<τ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
    (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ))
    {w:ℝ×S→ℝ} (hw:Measurable w)
    (hwcurve:∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t:S→ℝ))
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (s a:ℝ):
    MemLp (physicalCutoffSource halfEndBasicAnnulus χ
      (weightedPhysicalDilation s (cylinderLift w)) s a) 2 volume:=by
  exact physicalCutoffSource_memLp_two halfEndBasicAnnulus_isOpen
    nativeBasicAnnulus_precompact_off_zero.1 χ hχ
    ((nativeLocalH2_weighted_basicAnnulus (nativeOuter_same_curve_local_H2 b ht F d n σ hσ hw hwcurve) s).le_of_le (by norm_num:1≤2)) s a

#print axioms nativeBasicAnnulus_precompact_off_zero
#print axioms nativeLocalH2_weighted_basicAnnulus
#print axioms nativeOuter_same_curve_local_H2
#print axioms nativeOuter_same_curve_cutoff_source_L2
end Yamabe3.Analysis.SpherePolar
