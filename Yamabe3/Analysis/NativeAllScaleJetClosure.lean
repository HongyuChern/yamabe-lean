import Yamabe3.Analysis.NativeL2HalfAllScaleCLM
import Yamabe3.Analysis.NativeL2CollarJetClosure

/-! Actual C2 approximation of all scaled jets. The closure is inherited
from strong sums and the dense all-L2 source extension, without assuming
an approximation witness for the output field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|) ≤ κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|) ≤ κ)

def nativeL2ParticularGeneralRawJetCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus).prod
    ((ContinuousLinearMap.pi (nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus)).prod
      (ContinuousLinearMap.pi (fun k => ContinuousLinearMap.pi
        (nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus k))))

theorem nativeL2ParticularGeneralRawJet_mem
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2ParticularGeneralRawJetCLM hκ0 hκ1 V hminus hplus F ∈ nativeCollarJetClosure := by
  have hc := nativeC2CollarJetLinear.range.isClosed_topologicalClosure.preimage
    (nativeL2ParticularGeneralRawJetCLM hκ0 hκ1 V hminus hplus).continuous
  refine (continuousL2SourceInclusion_dense (SpectralSpace AngularIndex)).induction_on F hc ?_
  intro H
  let u : AngularIndex → nativeC2OffZero := fun i =>
    ⟨nativeL2ParticularMode hκ0 hκ1 V hminus H.val i,
      nativeL2ParticularMode_C2 hκ0 hκ1 V hminus hplus H.val H.property i⟩
  have hs := nativeL2ParticularCollar_modes_summable hκ0 hκ1 V hminus hplus H.val H.property
  have hm := nativeCollarJet_series_mem u hs.1 hs.2.1 hs.2.2
  have ha := nativeL2ParticularCLM_agrees_continuous hκ0 hκ1 V hminus hplus H
  change (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus (continuousL2SourceInclusion _ H),
    (fun j => nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus j (continuousL2SourceInclusion _ H)),
    (fun k j => nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus k j (continuousL2SourceInclusion _ H))) ∈ _
  simp_rw [ha.1,ha.2.1,ha.2.2]
  exact hm

theorem nativeFreeTailRawJet_mem (s : ℝ) (hs : 1 ≤ s) (b : SpectralSpace AngularIndex) :
    (nativeFreeTailValue s b,nativeFreeTailFirst s b,nativeFreeTailSecond s b) ∈ nativeCollarJetClosure := by
  have h := nativeFreeTail_summable s hs b
  exact nativeCollarJet_series_mem (fun i => ⟨_,nativeFreeTailMode_C2 s b i⟩) h.1 h.2.1 h.2.2

theorem nativeShiftedEntranceRawJet_mem (P : NativeHighPotential) (s : ℝ) (hs : s ≤ 2)
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    (nativeShiftedEntranceValue P s b,nativeShiftedEntranceFirst P s b,nativeShiftedEntranceSecond P s b) ∈ nativeCollarJetClosure := by
  have h := nativeShiftedEntrance_summable P s hs b hb
  exact nativeCollarJet_series_mem (fun i => ⟨_,nativeShiftedEntranceMode_C2 P s b i⟩) h.1 h.2.1 h.2.2

variable (P : NativeHighPotential)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)

theorem nativePoissonAllScaleRawJet_mem (s : ℝ) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    (nativePoissonAllScaleValue P hp s b,nativePoissonAllScaleFirst P hp s b,
      nativePoissonAllScaleSecond P hp s b) ∈ nativeCollarJetClosure := by
  change (nativePoissonAllScaleValue P hp s b,(fun j => nativePoissonAllScaleFirst P hp s b j),
    (fun k j => nativePoissonAllScaleSecond P hp s b k j)) ∈ _
  by_cases hs : s ≤ 2
  · simpa only [nativePoissonAllScaleValue,nativePoissonAllScaleFirst,nativePoissonAllScaleSecond,if_pos hs] using
      nativeShiftedEntranceRawJet_mem P s hs b hb
  · have hf := nativeFreeTailRawJet_mem s (by linarith) (nativePoissonAuxiliary P b)
    have hc := nativeL2ParticularGeneralRawJet_mem P.κ_nonneg P.κ_lt_one
      (boundedTimeTranslate ℝ s P.potential) (translated_kernel_bound P.potential P.kernel_bound s)
      (translated_kernel_bound P.potential hp s)
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s (nativePoissonL2CorrectionSource P b))
    simp only [nativePoissonAllScaleValue,nativePoissonAllScaleFirst,nativePoissonAllScaleSecond,if_neg hs]
    exact nativeCollarJetClosure.sub_mem hf hc

def nativeL2HalfAllScaleRawJetCLM (s : ℝ) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  (nativeL2HalfAllScaleValueCLM P hp s).prod
    ((ContinuousLinearMap.pi (nativeL2HalfAllScaleFirstCLM P hp s)).prod
      (ContinuousLinearMap.pi (fun k => ContinuousLinearMap.pi (nativeL2HalfAllScaleSecondCLM P hp s k))))

theorem nativeL2HalfAllScaleRawJet_mem (s : ℝ)
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfAllScaleRawJetCLM P hp s F ∈ nativeCollarJetClosure := by
  have hf := nativeL2ParticularGeneralRawJet_mem P.κ_nonneg P.κ_lt_one
    (boundedTimeTranslate ℝ s P.potential) (translated_kernel_bound P.potential P.kernel_bound s)
    (translated_kernel_bound P.potential hp s) (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)
  have hc := nativePoissonAllScaleRawJet_mem P hp s (nativeL2HalfEntrance P hp F)
    (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F).2.1
  exact nativeCollarJetClosure.sub_mem hf hc

def nativeL2HalfAllScaleJetCLM (s : ℝ) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  (nativeL2HalfAllScaleRawJetCLM P hp s).codRestrict nativeCollarJetClosure (nativeL2HalfAllScaleRawJet_mem P hp s)

theorem nativeL2HalfAllScaleJet_zero_eq_original
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfAllScaleJetCLM P hp 0 F=nativeL2HalfJetCLM P hp F := by
  apply Subtype.ext
  have h := nativeL2HalfAllScale_zero_eq_original P hp F
  exact Prod.ext h.1 (Prod.ext (funext h.2.1) (funext (fun k => funext (h.2.2 k))))

#print axioms nativeL2ParticularGeneralRawJet_mem
#print axioms nativeFreeTailRawJet_mem
#print axioms nativeShiftedEntranceRawJet_mem
#print axioms nativePoissonAllScaleRawJet_mem
#print axioms nativeL2HalfAllScaleRawJet_mem
#print axioms nativeL2HalfAllScaleJet_zero_eq_original
end Yamabe3.Analysis.SpherePolar
