import Yamabe3.Analysis.NativeParticularFiniteNormal
import Yamabe3.Analysis.NativeTraceAngularCoordinates

/-! The actual collar normal trace has a proved half-order spectral
budget for every L2 source. Its identification is made through strong
finite physical jets and then dense source extension. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (P : NativeHighPotential)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

def nativeL2ParticularNormalAngularCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] AngularL2 :=
  nativeTraceAngularCLM.comp (nativeCollarNormalTraceCLM.comp (nativeL2ParticularJetCLM P hp))

theorem nativeL2ParticularJet_normal_trace_continuous
    (H : continuousL2Source (SpectralSpace AngularIndex)) :
    nativeCollarNormalTraceCLM (nativeL2ParticularJetCLM P hp (continuousL2SourceInclusion _ H))=
      nativeAngularTraceCLM (nativeContinuousParticularNormal P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val) := by
  let u : AngularIndex → nativeC2OffZero := fun i =>
    ⟨nativeL2ParticularMode P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val i,
      nativeL2ParticularMode_C2 P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp H.val H.property i⟩
  have hs := nativeL2ParticularCollar_modes_summable P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp H.val H.property
  have ha := nativeL2ParticularCLM_agrees_continuous P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp H
  have hJ : (nativeL2ParticularJetCLM P hp (continuousL2SourceInclusion _ H)).val=
      ((∑' i,nativeC2CollarValue (u i).property),
        (fun j => ∑' i,nativeC2CollarFirst (u i).property j),
        (fun k j => ∑' i,nativeC2CollarSecond (u i).property k j)) := by
    change (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp (continuousL2SourceInclusion _ H),
      (fun j => nativeL2ParticularFirstCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp j (continuousL2SourceInclusion _ H)),
      (fun k j => nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp k j (continuousL2SourceInclusion _ H)))=_
    simp_rw [ha.1,ha.2.1,ha.2.2]
    rfl
  let N := nativeContinuousParticularNormal P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val
  apply nativeCollarNormalTrace_of_C2_limit (l := atTop) (fun s : Finset AngularIndex => ∑ i ∈ s,u i)
    (nativeL2ParticularJetCLM P hp (continuousL2SourceInclusion _ H))
  · rw [hJ]
    exact nativeC2CollarJet_series_tendsto u hs.1 hs.2.1 hs.2.2
  · have ht := nativeAngularTraceCLM.continuous.continuousAt.tendsto.comp
      (finiteHilbertProjection_tendsto_filter angularBasis tendsto_id N)
    apply ht.congr'
    apply Eventually.of_forall
    intro s
    symm
    apply Lp.ext
    filter_upwards [nativeC2NormalTraceLinear_ae (∑ i ∈ s,u i),
      nativeL2ParticularFinite_normal_trace_ae P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val s,
      nativeAngularTraceCLM_ae (finiteHilbertProjection angularBasis s N)] with θ hu hn hm
    simp only [Function.comp_apply,id_eq]
    rw [hu,hm]
    have he : (∑ i ∈ s,u i).val=(fun x => ∑ i ∈ s,nativeL2ParticularMode P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val i x) := by
      funext x
      simp only [Submodule.coe_sum,Finset.sum_apply,u]
    rw [he]
    exact hn

theorem nativeL2ParticularNormalAngular_half_bound
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    NativeAngularSpectralRegular (1/2) (nativeL2ParticularNormalAngularCLM P hp F) ∧
      (∑' i,nativeAngularWeightedSquare (1/2) (nativeL2ParticularNormalAngularCLM P hp F) i)≤
        (50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2*‖F‖^2 := by
  apply nativeAngularSpectral_bound_of_dense (continuousL2SourceInclusion _)
    (continuousL2SourceInclusion_dense _) (nativeL2ParticularNormalAngularCLM P hp)
    (1/2) ((50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2) _ F
  intro H
  have he : nativeL2ParticularNormalAngularCLM P hp (continuousL2SourceInclusion _ H)=
      nativeContinuousParticularNormal P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val := by
    change nativeTraceAngularCLM (nativeCollarNormalTraceCLM (nativeL2ParticularJetCLM P hp (continuousL2SourceInclusion _ H)))=_
    rw [nativeL2ParticularJet_normal_trace_continuous,nativeTraceAngular_left_inverse]
  rw [he]
  exact nativeContinuousParticularNormal_half_bound P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp H.val H.property

#print axioms nativeL2ParticularJet_normal_trace_continuous
#print axioms nativeL2ParticularNormalAngular_half_bound
end Yamabe3.Analysis.SpherePolar
