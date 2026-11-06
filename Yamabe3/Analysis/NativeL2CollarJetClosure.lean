import Yamabe3.Analysis.NativeCollarJetLimits
import Yamabe3.Analysis.NativeL2HalfCollarCLM

/-! The actual particular and same-source Poisson-corrected collar jets
belong to the genuine strong C2 jet closure. The dense source extension
preserves this closed property. No Sobolev approximation witness is input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

def nativeL2ParticularRawJetCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus).prod
    ((ContinuousLinearMap.pi (nativeL2ParticularFirstCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus)).prod
      (ContinuousLinearMap.pi (fun k => ContinuousLinearMap.pi
        (nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus k))))

theorem nativeL2ParticularRawJet_mem
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2ParticularRawJetCLM P hplus F ∈ nativeCollarJetClosure := by
  have hc := nativeC2CollarJetLinear.range.isClosed_topologicalClosure.preimage
    (nativeL2ParticularRawJetCLM P hplus).continuous
  refine (continuousL2SourceInclusion_dense (SpectralSpace AngularIndex)).induction_on F hc ?_
  intro H
  let u : AngularIndex → nativeC2OffZero := fun i =>
    ⟨nativeL2ParticularMode P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val i,
      nativeL2ParticularMode_C2 P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus H.val H.property i⟩
  have hs := nativeL2ParticularCollar_modes_summable P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus H.val H.property
  have hm := nativeCollarJet_series_mem u hs.1 hs.2.1 hs.2.2
  have ha := nativeL2ParticularCLM_agrees_continuous P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus H
  change (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus (continuousL2SourceInclusion _ H),
    (fun j => nativeL2ParticularFirstCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus j (continuousL2SourceInclusion _ H)),
    (fun k j => nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus k j (continuousL2SourceInclusion _ H))) ∈ _
  simp_rw [ha.1,ha.2.1,ha.2.2]
  exact hm

def nativeL2ParticularJetCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  (nativeL2ParticularRawJetCLM P hplus).codRestrict nativeCollarJetClosure (nativeL2ParticularRawJet_mem P hplus)

theorem nativePoissonRawJet_mem (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    (nativePoissonCollarValue P b,nativePoissonCollarFirst P b,nativePoissonCollarSecond P b) ∈ nativeCollarJetClosure := by
  let u : AngularIndex → nativeC2OffZero := fun i => ⟨nativePoissonCollarMode P b i,nativePoissonCollarMode_C2 P b i⟩
  have hs := nativePoissonCollar_modes_summable P b hb
  exact nativeCollarJet_series_mem u hs.1 hs.2.1 hs.2.2

def nativePoissonCollarJet (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) : nativeCollarJetClosure :=
  ⟨(nativePoissonCollarValue P b,nativePoissonCollarFirst P b,nativePoissonCollarSecond P b),nativePoissonRawJet_mem P b hb⟩

def nativeL2HalfRawJetCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  (nativeL2HalfCollarValueCLM P hplus).prod
    ((ContinuousLinearMap.pi (nativeL2HalfCollarFirstCLM P hplus)).prod
      (ContinuousLinearMap.pi (fun k => ContinuousLinearMap.pi (nativeL2HalfCollarSecondCLM P hplus k))))

theorem nativeL2HalfRawJet_mem
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfRawJetCLM P hplus F ∈ nativeCollarJetClosure := by
  have hb := (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F).2.1
  exact nativeCollarJetClosure.sub_mem (nativeL2ParticularRawJet_mem P hplus F)
    (nativePoissonRawJet_mem P (nativeL2HalfEntrance P hplus F) hb)

def nativeL2HalfJetCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  (nativeL2HalfRawJetCLM P hplus).codRestrict nativeCollarJetClosure (nativeL2HalfRawJet_mem P hplus)

theorem nativeL2HalfJet_eq_difference
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfJetCLM P hplus F=nativeL2ParticularJetCLM P hplus F-
      nativePoissonCollarJet P (nativeL2HalfEntrance P hplus F)
        (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F).2.1 := by
  apply Subtype.ext
  rfl

#print axioms nativeL2ParticularRawJet_mem
#print axioms nativePoissonRawJet_mem
#print axioms nativeL2HalfRawJet_mem
#print axioms nativeL2HalfJet_eq_difference
end Yamabe3.Analysis.SpherePolar
