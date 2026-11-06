import Yamabe3.Analysis.NativeLowReverseSourceBinding

/-! A bounded full-line source preprocessor adapted to a proven lower
support bound. It cancels the reverse fourth-power weight on the actual
source everywhere, not only on the fixed collar. Cutoff independence is
proved for supported sources; no source integrability is postulated. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeSupportedReverseWeight (b : ℝ) : ℝ→ᵇℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => Real.exp (-4*max b t))
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.max continuous_id)))
    (Real.exp (-4*b)) (fun t => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_le_exp]
      linarith [le_max_left b t])

theorem nativeSupportedReverseWeight_eq (b t : ℝ) (ht : b≤t) :
    nativeSupportedReverseWeight b t=Real.exp (-4*t) := by
  change Real.exp (-4*max b t)=_
  rw [max_eq_right ht]

theorem nativeSupportedReverseWeight_norm (b : ℝ) :
    ‖nativeSupportedReverseWeight b‖≤Real.exp (-4*b) := by
  apply (BoundedContinuousFunction.norm_le (Real.exp_pos _).le).mpr
  intro t
  change ‖Real.exp (-4*max b t)‖≤_
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_le_exp]
  linarith [le_max_left b t]

def nativeSupportedReverseSourcePrepareCLM (b : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  (l2TimeReflectCLM AngularSpectralSpace).comp (spectralL2PotentialMulCLM (nativeSupportedReverseWeight b))

theorem nativeSupportedReverseSourcePrepare_bound (b : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ‖nativeSupportedReverseSourcePrepareCLM b F‖≤Real.exp (-4*b)*‖F‖ := by
  change ‖l2TimeReflectCLM AngularSpectralSpace (spectralL2PotentialMulCLM (nativeSupportedReverseWeight b) F)‖≤_
  rw [l2TimeReflect_norm]
  exact (spectralL2PotentialMul_norm_le (nativeSupportedReverseWeight b) F).trans
    (mul_le_mul_of_nonneg_right (nativeSupportedReverseWeight_norm b) (norm_nonneg _))

theorem nativeSupportedReverseSourcePrepare_ae (b : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) :
    (fun t : ℝ => nativeSupportedReverseSourcePrepareCLM b F (-t))=ᵐ[volume]
      (fun t => Real.exp (-4*t) • F t) := by
  have hr := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (l2TimeReflect_ae AngularSpectralSpace (spectralL2PotentialMulCLM (nativeSupportedReverseWeight b) F))
  filter_upwards [hr,spectralL2PotentialMul_coe_ae (nativeSupportedReverseWeight b) F,hF] with t hr hm hf
  change nativeSupportedReverseSourcePrepareCLM b F (-t)=_
  change l2TimeReflectCLM AngularSpectralSpace (spectralL2PotentialMulCLM (nativeSupportedReverseWeight b) F) (-t)=_
  change spectralL2PotentialMulCLM (nativeSupportedReverseWeight b) F t=nativeSupportedReverseWeight b t • F t at hm
  rw [hr,neg_neg,hm]
  by_cases ht : b≤t
  · rw [nativeSupportedReverseWeight_eq b t ht]
  · rw [hf (lt_of_not_ge ht),smul_zero,smul_zero]

theorem nativeSupportedReverseSource_exact_cancellation (b : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) :
    (fun t : ℝ => Real.exp (4*t) • nativeSupportedReverseSourcePrepareCLM b F (-t))=ᵐ[volume]
      (F : ℝ→AngularSpectralSpace) := by
  filter_upwards [nativeSupportedReverseSourcePrepare_ae b F hF] with t ht
  rw [ht,smul_smul,←Real.exp_add,show 4*t+-4*t=0 by ring,Real.exp_zero,one_smul]

theorem nativeSupportedReverseSource_cutoff_independent (b c : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hb : ∀ᵐt : ℝ ∂volume,t<b → F t=0)
    (hc : ∀ᵐt : ℝ ∂volume,t<c → F t=0) :
    nativeSupportedReverseSourcePrepareCLM b F=nativeSupportedReverseSourcePrepareCLM c F := by
  have he := (nativeSupportedReverseSourcePrepare_ae b F hb).trans
    (nativeSupportedReverseSourcePrepare_ae c F hc).symm
  have hr := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae he
  apply Lp.ext
  filter_upwards [hr] with t ht
  change nativeSupportedReverseSourcePrepareCLM b F t=nativeSupportedReverseSourcePrepareCLM c F t
  simpa only [neg_neg] using ht

theorem nativeSupportedReverseSource_collar_reconstruction (b : ℝ) (hb : b≤ -(1/2:ℝ))
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowReverseL2SourceCLM (nativeSupportedReverseSourcePrepareCLM b F)=nativeL2LowPhysicalSourceCLM F := by
  change nativeInverseFourthPowerCollarCLM
    (nativeL2LowPhysicalSourceCLM (l2TimeReflectCLM AngularSpectralSpace
      (l2TimeReflectCLM AngularSpectralSpace (spectralL2PotentialMulCLM (nativeSupportedReverseWeight b) F))))=_
  rw [l2TimeReflect_involution]
  apply Lp.ext
  filter_upwards [nativeCollarLocalMulCLM_ae (fun x => (‖x‖^4)⁻¹) nativeInverseFourthPower_continuousOn
    (nativeL2LowPhysicalSourceCLM (spectralL2PotentialMulCLM (nativeSupportedReverseWeight b) F)),
    nativeLowL2PhysicalSource_weight_ae (nativeSupportedReverseWeight b) F,
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hm hw hx
  change nativeCollarLocalMulCLM (fun x => (‖x‖^4)⁻¹) nativeInverseFourthPower_continuousOn
    (nativeL2LowPhysicalSourceCLM (spectralL2PotentialMulCLM (nativeSupportedReverseWeight b) F)) x=_
  rw [hm,hw]
  have ht : b≤ -Real.log ‖x‖ := by
    rcases hx with ⟨hx0,ht⟩
    change -(1/2:ℝ)< -Real.log ‖x‖ ∧ -Real.log ‖x‖<1/2 at ht
    linarith [ht.1]
  have hn : 0<‖x‖ := norm_pos_iff.mpr (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx))
  have he : nativeSupportedReverseWeight b (-Real.log ‖x‖)=‖x‖^4 := by
    rw [nativeSupportedReverseWeight_eq b _ ht]
    calc
      _ = Real.exp (Real.log ‖x‖+Real.log ‖x‖+Real.log ‖x‖+Real.log ‖x‖) := by congr 1;ring
      _ = _ := by simp only [Real.exp_add,Real.exp_log hn];ring
  rw [he,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero 4 (ne_of_gt hn)),one_mul]

#print axioms nativeSupportedReverseWeight_eq
#print axioms nativeSupportedReverseWeight_norm
#print axioms nativeSupportedReverseSourcePrepare_bound
#print axioms nativeSupportedReverseSourcePrepare_ae
#print axioms nativeSupportedReverseSource_exact_cancellation
#print axioms nativeSupportedReverseSource_cutoff_independent
#print axioms nativeSupportedReverseSource_collar_reconstruction
end Yamabe3.Analysis.SpherePolar
