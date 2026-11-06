import Yamabe3.Analysis.NativeSupportedOuterNewtonAnnulus
import Yamabe3.Analysis.NativeCollarLiftRepresentative
import Yamabe3.Analysis.WeightedH4RepresentativeTransport
import Yamabe3.Analysis.NativePhysicalCutoffSourceIdentity

/-! Same-curve representatives determine the same volume field and the
same physical cutoff residual. Actual far representatives have L2 cutoff
sources; no choice of a different solution is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem native_lift_ae_eq_of_joint_slices
    {w z:ℝ×S→ℝ} (hw:Measurable w) (hz:Measurable z)
    (hae:∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](fun θ=>z (t,θ))) :
    cylinderLift w=ᵐ[volume]cylinderLift z:=by
  let C:ℕ→Set E:=fun n=>cylinderShell (-(n:ℝ)) (n:ℝ)
  have hcover:(⋃n,C n)=({0}ᶜ:Set E):=by
    ext x
    constructor
    · intro hx
      obtain ⟨n,hn⟩:=mem_iUnion.mp hx
      exact cylinderShell_ne_zero hn
    · intro hx
      have hn:0<‖x‖:=norm_pos_iff.mpr hx
      obtain ⟨n,hnn⟩:=exists_nat_gt |Real.log ‖x‖|
      apply mem_iUnion.mpr
      refine ⟨n,?_⟩
      change Real.exp (-(n:ℝ))≤‖x‖ ∧ ‖x‖≤Real.exp (-(-(n:ℝ)))
      rw [←Real.exp_log hn]
      constructor
      · apply Real.exp_le_exp.mpr
        linarith [neg_abs_le (Real.log ‖x‖)]
      · apply Real.exp_le_exp.mpr
        linarith [le_abs_self (Real.log ‖x‖)]
  have hC:cylinderLift w=ᵐ[volume.restrict (⋃n,C n)]cylinderLift z:=
    (ae_eq_restrict_iUnion_iff C _ _).mpr (fun n=>native_shell_lift_ae_eq_of_joint_slices hw hz hae _ _)
  rw [hcover] at hC
  have h:=(ae_restrict_iff' isClosed_singleton.isOpen_compl.measurableSet).mp hC
  filter_upwards [h,volume.ae_ne (0:E)] with x hx hx0
  exact hx hx0

theorem physicalCutoffSource_congr_ae {O:Set E} (hO:IsOpen O)
    (χ:E→ℝ) {u v:E→ℝ} (huv:u=ᵐ[volume.restrict O]v) (s a:ℝ):
    physicalCutoffSource O χ u s a=ᵐ[volume]physicalCutoffSource O χ v s a:=by
  have hd(i:Fin 3):=chosenWeakPartial'_ae_congr (by norm_num:(1:ℝ≥0∞)≤2) hO huv i
  have he:weakCutoffCommutator O χ u=ᵐ[volume.restrict O]weakCutoffCommutator O χ v:=by
    filter_upwards [huv,ae_all_iff.mpr hd] with x hx hdx
    simp only [weakCutoffCommutator,hx,hdx]
  have hi:O.indicator (weakCutoffCommutator O χ u)=ᵐ[volume]
      O.indicator (weakCutoffCommutator O χ v):=by
    have hh:=(ae_restrict_iff' hO.measurableSet).mp he
    filter_upwards [hh] with x hx
    by_cases hxO:x∈O
    · simp only [indicator_of_mem hxO,hx hxO]
    · simp only [indicator_of_notMem hxO]
  have hh:=ae_comp_dilation (Real.exp_ne_zero (s-Real.log a))
    (ae_restrict_of_ae (s:=univ) hi)
  simp only [preimage_univ,Measure.restrict_univ] at hh
  filter_upwards [hh] with x hx
  unfold physicalCutoffSource physicalCutoffAnnulus
  by_cases ho:Real.exp (s-Real.log a) • x∈O
  · simpa only [indicator_of_mem ho,indicator_of_mem (show x∈(fun y:E=>Real.exp (s-Real.log a) • y)⁻¹' O from ho)]
      using congrArg (fun r:ℝ=>8*Real.exp (-2*Real.log a+s/2)*r) hx
  · simp only [indicator_of_notMem ho,indicator_of_notMem (show x∉(fun y:E=>Real.exp (s-Real.log a) • y)⁻¹' O from ho)]

theorem physicalCutoffSource_memLp_two
    {O:Set E} (hO:IsOpen O) (hOc:IsCompact (closure O))
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) {u:E→ℝ} (hu:MemWkp 1 2 u O) (s a:ℝ):
    MemLp (physicalCutoffSource O χ u s a) 2 volume:=by
  obtain ⟨C,hC,hbound⟩:=exists_weakCutoffCommutator_L2_bound hO hOc χ hχ
  have hmem:MemLp (O.indicator (weakCutoffCommutator O χ u)) 2 volume:=
    (memLp_indicator_iff_restrict hO.measurableSet).mpr (hbound u hu).1
  have hscale:MemLp (fun x:E=>(O.indicator (weakCutoffCommutator O χ u))
      (Real.exp (s-Real.log a) • x)) 2 volume:=by
    simpa only [preimage_univ,Measure.restrict_univ] using
      memLp_comp_dilation (Real.exp_ne_zero (s-Real.log a)) (hmem.restrict univ)
  apply (hscale.const_mul (8*Real.exp (-2*Real.log a+s/2))).ae_eq
  filter_upwards [] with x
  unfold physicalCutoffSource physicalCutoffAnnulus
  by_cases ho:Real.exp (s-Real.log a) • x∈O
  · simp only [indicator_of_mem ho,indicator_of_mem (show x∈(fun y:E=>Real.exp (s-Real.log a) • y)⁻¹' O from ho)]
  · simp only [indicator_of_notMem ho,indicator_of_notMem (show x∉(fun y:E=>Real.exp (s-Real.log a) • y)⁻¹' O from ho),mul_zero]

theorem exists_nativeOuter_same_curve_H4_source (b:ℝ) {τ:ℝ} (ht:0<τ):
    ∃T:ℝ,T≤-(1/2:ℝ) ∧
      ∀(F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
        (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐt:ℝ ∂volume,t<b→F t=0)→
      ∀w:ℝ×S→ℝ,Measurable w→
      (∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t:S→ℝ))→
      ∀s:ℝ,s≤T→MemWkp 4 2 (weightedPhysicalDilation s (cylinderLift w)) halfEndBasicAnnulus:=by
  obtain ⟨T,hT,C,hC,hfield⟩:=exists_nativeSupportedOuter_same_field_Newton_annulus_H4 b ht
  refine ⟨T,hT,fun F d n σ hσ hF w hw hwcurve s hs=>?_⟩
  obtain ⟨z,hz,_,hzcurve,hzjet,hzreg⟩:=hfield F d n σ hσ hF
  have he:=native_lift_ae_eq_of_joint_slices hz hw (fun t=>(hzcurve t).trans (hwcurve t).symm)
  exact (MemWkp_congr_ae (by norm_num) halfEndBasicAnnulus_isOpen
    (weightedPhysicalDilation_congr_ae he s)).mp (hzreg s hs).1

#print axioms native_lift_ae_eq_of_joint_slices
#print axioms physicalCutoffSource_congr_ae
#print axioms physicalCutoffSource_memLp_two
#print axioms exists_nativeOuter_same_curve_H4_source
end Yamabe3.Analysis.SpherePolar
