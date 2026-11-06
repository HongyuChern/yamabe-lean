import Yamabe3.Analysis.NativeBubbleFullSupportedField

/-! Quantitative decay and all-scale source identities hold for the
same full bubble field and one joint representative. Constants precede
the source; the true physical radial factor exp(t/2) is retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem nativeReverseConjugatedCurve_norm_bound (W : ℝ→ᵇAngularL2) (t : ℝ) :
    ‖nativeReverseConjugatedCurve W t‖≤‖W‖*Real.exp (2*t) := by
  rw [nativeReverseConjugatedCurve,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left (W.norm_coe_le_norm (-t)) (Real.exp_pos _).le).trans_eq (mul_comm _ _)

theorem exists_nativeBubbleFullSupported_decay_bound (τ b : ℝ) :
    ∃D : ℝ,0≤D ∧ ∀F : Lp AngularSpectralSpace 2 (volume : Measure ℝ),
      (∀ᵐs : ℝ ∂volume,s<b → F s=0) → ∀t : ℝ,
      ‖nativeBubbleFullSupportedCurve τ b F t‖≤D*‖F‖*Real.exp (2*t) ∧
      ‖Real.exp (t/2) • nativeBubbleFullSupportedCurve τ b F t‖≤D*‖F‖*Real.exp (5*t/2) := by
  obtain ⟨D,hD,hd⟩ := exists_nativeBubbleParticular_far_end_bound τ b
  let L := nativeLowL2AngularCLM (nativeBubbleReverseProfile τ)
    (nativeBubbleReverseProfile_continuous τ) (nativeBubbleReverseProfile_bounds τ)
  let C := D+‖L‖*Real.exp (-4*b)
  have hC : 0≤C := by dsimp only [C];positivity
  refine ⟨C,hC,fun F hF t => ?_⟩
  have hL := (L.le_opNorm (nativeSupportedReverseSourcePrepareCLM b F)).trans
    (mul_le_mul_of_nonneg_left (nativeSupportedReverseSourcePrepare_bound b F) (norm_nonneg L))
  have hl := (nativeReverseConjugatedCurve_norm_bound (L (nativeSupportedReverseSourcePrepareCLM b F)) t).trans
    (mul_le_mul_of_nonneg_right hL (Real.exp_pos _).le)
  have h : ‖nativeBubbleFullSupportedCurve τ b F t‖≤C*‖F‖*Real.exp (2*t) :=
    ((norm_add_le _ _).trans (add_le_add (hd F hF t) hl)).trans_eq (by dsimp only [C];ring)
  refine ⟨h,?_⟩
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq
  calc
    _ = C*‖F‖*(Real.exp (t/2)*Real.exp (2*t)) := by ring
    _ = _ := by rw [←Real.exp_add];congr 2;ring

theorem nativeBubbleFullSupported_decay (τ b : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐs : ℝ ∂volume,s<b → F s=0) :
    Tendsto (nativeBubbleFullSupportedCurve τ b F) atBot (𝓝 0) ∧
      Tendsto (fun t => Real.exp (t/2) • nativeBubbleFullSupportedCurve τ b F t) atBot (𝓝 0) := by
  obtain ⟨D,hD,hd⟩ := exists_nativeBubbleFullSupported_decay_bound τ b
  have he (a : ℝ) (ha : 0<a) : Tendsto (fun t : ℝ => Real.exp (a*t)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos ha).2 tendsto_id)
  constructor
  · apply squeeze_zero_norm' (Eventually.of_forall fun t => (hd F hF t).1)
    simpa using (he 2 (by norm_num)).const_mul (D*‖F‖)
  · apply squeeze_zero_norm' (Eventually.of_forall fun t => (hd F hF t).2)
    have h := (he (5/2) (by norm_num)).const_mul (D*‖F‖)
    convert h using 1 <;> ext t <;> congr 2 <;> ring

theorem exists_nativeBubbleFullSupported_same_field_equation_and_decay (τ b : ℝ) :
    ∃D : ℝ,0≤D ∧ ∀F : Lp AngularSpectralSpace 2 (volume : Measure ℝ),
      (∀ᵐt : ℝ ∂volume,t<b → F t=0) →
      ∃w : ℝ×S→ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) ∧
      (∀t,(fun θ => w (t,θ))=ᵐ[angularVolume](nativeBubbleFullSupportedCurve τ b F t : S→ℝ)) ∧
      (∀t,‖nativeBubbleFullSupportedCurve τ b F t‖≤D*‖F‖*Real.exp (2*t) ∧
        ‖Real.exp (t/2) • nativeBubbleFullSupportedCurve τ b F t‖≤D*‖F‖*Real.exp (5*t/2)) ∧
      (∀s : ℝ,((nativeBubbleFullSupportedAllScaleRawJetCLM τ b s F).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) ∧
        nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
          (nativeBubbleFullSupportedAllScaleRawJetCLM τ b s F)=
            -nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F)) ∧
      Tendsto (fun t => Real.exp (t/2) • nativeBubbleFullSupportedCurve τ b F t) atBot (𝓝 0) := by
  obtain ⟨D,hD,hd⟩ := exists_nativeBubbleFullSupported_decay_bound τ b
  refine ⟨D,hD,fun F hF => ?_⟩
  obtain ⟨w,hw,hl,hae,hj⟩ := exists_nativeBubbleFullSupported_same_source_localH2 τ b F hF
  exact ⟨w,hw,hl,hae,hd F hF,hj,(nativeBubbleFullSupported_decay τ b F hF).2⟩

#print axioms nativeReverseConjugatedCurve_norm_bound
#print axioms exists_nativeBubbleFullSupported_decay_bound
#print axioms nativeBubbleFullSupported_decay
#print axioms exists_nativeBubbleFullSupported_same_field_equation_and_decay
end Yamabe3.Analysis.SpherePolar
