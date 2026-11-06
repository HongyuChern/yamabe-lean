import Yamabe3.Analysis.NativeBubbleParticularFarEnd
import Yamabe3.Analysis.NativeExteriorL2HighDirichlet
import Yamabe3.Analysis.NativePoissonExteriorCollarIdentification

/-! The same exterior zero-value high solution now has its actual
continuous angular field and a quantitative far-end bound. The collar
jet and boundary cancellation are not replaced by another solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeExteriorL2HighCurve (P B : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (t : ℝ) : AngularL2 :=
  nativeConjugatedCurve (nativeL2ParticularAngularCLM P.potential F) t-
    nativePoissonExteriorCurve B
      (nativeL2EntranceH1 P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F) t

theorem nativeExteriorL2HighCurve_continuous (P B : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    Continuous (nativeExteriorL2HighCurve P B hp F) :=
  (nativeConjugatedCurve_continuous _).sub (nativePoissonExteriorCurve_continuous _ _)

theorem nativeExteriorL2HighCurve_same_collar (P B : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ∃w : ℝ×S→ℝ,Measurable w ∧
      (∀t,(fun θ => w (t,θ))=ᵐ[angularVolume](nativeExteriorL2HighCurve P B hp F t : S→ℝ)) ∧
      ((nativeExteriorL2HighJetCLM P B hp F).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        cylinderLift w := by
  let L := nativeL2ParticularAngularCLM P.potential F
  let b := nativeL2EntranceH1 P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F
  let p := nativeConjugatedJoint L
  obtain ⟨q,hq,hqa,_⟩ := nativePoissonExteriorCurve_joint_representative B b
  have hpj := nativeConjugatedJoint_measurable L
  have hpa := nativeConjugatedJoint_ae L
  have hpl := nativeL2ParticularValueCLM_eq_lift P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F hpj hpa
  have hql := nativePoissonExteriorCollarValue_eq_lift B b
    (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F).2.1 hq.measurable hqa
  refine ⟨fun z => p z-q z,hpj.sub hq.measurable,fun t => ?_,?_⟩
  · have hsub := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_sub (nativeConjugatedCurve L t) (nativePoissonExteriorCurve B b t))
    filter_upwards [hpa t,hqa t,hsub] with θ ht hqt hs
    change p (t,θ)=_ at ht
    change p (t,θ)-q (t,θ)=_
    rw [ht,hqt]
    exact (hs (mem_univ θ)).symm
  · rw [nativeExteriorL2HighJetCLM_eq]
    change ((nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F-
      nativePoissonExteriorCollarValue B b : NativeCollarL2) : E→ℝ)=ᵐ[_] _
    rw [cylinderLift_sub]
    filter_upwards [Lp.coeFn_sub
      (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F)
      (nativePoissonExteriorCollarValue B b),hpl,hql] with x hs hx hy
    rw [hs]
    change nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F x-
      nativePoissonExteriorCollarValue B b x=_
    rw [hx,hy]

theorem nativePoissonExteriorCurve_far_end_bound (B : NativeHighPotential) (b : AngularH1)
    (t : ℝ) (ht : t≤0) :
    ‖nativePoissonExteriorCurve B b t‖≤(‖b‖/(1-B.κ))*Real.exp (2*t) := by
  change ‖nativePoissonReflectedCurve B b (-t)‖≤_
  rw [nativePoissonReflectedCurve,if_pos (neg_nonneg.mpr ht)]
  have h := (nativeHalfHighPotentialPhysical_weighted_cauchy B.κ_nonneg B.κ_lt_one B.potential
    B.kernel_bound B.nonneg b (-t) (neg_nonneg.mpr ht)).1
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (2*t)).le
  have he : Real.exp (2*t)*Real.exp (2*(-t))=1 := by rw [←Real.exp_add];convert Real.exp_zero using 1 <;> ring
  rw [←mul_assoc,he,one_mul] at hh
  exact hh.trans_eq (mul_comm _ _)

theorem exists_nativeBubbleExteriorHigh_far_end_bound (τ b : ℝ) :
    ∃D : ℝ,0≤D ∧ ∀F : Lp AngularSpectralSpace 2 (volume : Measure ℝ),
      (∀ᵐs : ℝ ∂volume,s<b → F s=0) → ∀t : ℝ,t≤0 →
      ‖nativeExteriorL2HighCurve (fullBubbleHighPotential τ) (fullBubbleHighPotential (-τ))
        (fullBubblePhasePotential_plus_kernel τ) F t‖≤D*‖F‖*Real.exp (2*t) := by
  obtain ⟨D,hD,hd⟩ := exists_nativeBubbleParticular_far_end_bound τ b
  let P := fullBubbleHighPotential τ
  let B := fullBubbleHighPotential (-τ)
  let T := nativeL2EntranceH1CLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound
    (fullBubblePhasePotential_plus_kernel τ)
  have hκ : 0<1-B.κ := sub_pos.mpr B.κ_lt_one
  refine ⟨D+‖T‖/(1-B.κ),by positivity,fun F hF t ht => ?_⟩
  have hq := nativePoissonExteriorCurve_far_end_bound B (T F) t ht
  have hn : ‖T F‖/(1-B.κ)≤(‖T‖*‖F‖)/(1-B.κ) :=
    div_le_div_of_nonneg_right (T.le_opNorm F) hκ.le
  have hq' := hq.trans (mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le)
  change ‖nativeConjugatedCurve (nativeL2ParticularAngularCLM (fullBubblePhasePotential τ) F) t-
    nativePoissonExteriorCurve B (T F) t‖≤_
  exact ((norm_sub_le _ _).trans (add_le_add (hd F hF t) hq')).trans_eq (by ring)

theorem nativeBubbleExteriorHighCurve_tendsto_bot (τ b : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐs : ℝ ∂volume,s<b → F s=0) :
    Tendsto (nativeExteriorL2HighCurve (fullBubbleHighPotential τ) (fullBubbleHighPotential (-τ))
      (fullBubblePhasePotential_plus_kernel τ) F) atBot (𝓝 0) := by
  obtain ⟨D,hD,hd⟩ := exists_nativeBubbleExteriorHigh_far_end_bound τ b
  apply squeeze_zero_norm' (by filter_upwards [eventually_le_atBot (0:ℝ)] with t ht;exact hd F hF t ht)
  have he : Tendsto (fun t : ℝ => Real.exp (2*t)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ)<2)).2 tendsto_id)
  simpa using he.const_mul (D*‖F‖)

#print axioms nativeExteriorL2HighCurve_continuous
#print axioms nativeExteriorL2HighCurve_same_collar
#print axioms nativePoissonExteriorCurve_far_end_bound
#print axioms exists_nativeBubbleExteriorHigh_far_end_bound
#print axioms nativeBubbleExteriorHighCurve_tendsto_bot
end Yamabe3.Analysis.SpherePolar
