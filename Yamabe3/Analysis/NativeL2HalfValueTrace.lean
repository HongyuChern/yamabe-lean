import Yamabe3.Analysis.NativeL2CollarJetClosure
import Yamabe3.Analysis.NativeCollarSeriesValueTrace

/-! The same all-L2 source field has actual zero value trace in the
constructed collar trace operator. This is obtained from finite C2
restrictions, source density and the same Poisson entrance cancellation. -/
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

theorem nativeL2ParticularJet_value_trace
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeCollarValueTraceCLM (nativeL2ParticularJetCLM P hplus F)=
      nativeAngularTraceCLM (nativeL2ParticularAngularCLM P.potential F 0) := by
  have hc := isClosed_eq
    (nativeCollarValueTraceCLM.continuous.comp (nativeL2ParticularJetCLM P hplus).continuous)
    (nativeAngularTraceCLM.continuous.comp ((BoundedContinuousFunction.evalCLM ℝ 0).continuous.comp
      (nativeL2ParticularAngularCLM P.potential).continuous))
  refine (continuousL2SourceInclusion_dense (SpectralSpace AngularIndex)).induction_on F hc ?_
  intro H
  let u : AngularIndex → nativeC2OffZero := fun i =>
    ⟨nativeL2ParticularMode P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val i,
      nativeL2ParticularMode_C2 P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus H.val H.property i⟩
  have hs := nativeL2ParticularCollar_modes_summable P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus H.val H.property
  have ha := nativeL2ParticularCLM_agrees_continuous P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus H
  have hJ : (nativeL2ParticularJetCLM P hplus (continuousL2SourceInclusion _ H)).val=
      ((∑' i,nativeC2CollarValue (u i).property),
        (fun j => ∑' i,nativeC2CollarFirst (u i).property j),
        (fun k j => ∑' i,nativeC2CollarSecond (u i).property k j)) := by
    change (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus (continuousL2SourceInclusion _ H),
      (fun j => nativeL2ParticularFirstCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus j (continuousL2SourceInclusion _ H)),
      (fun k j => nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus k j (continuousL2SourceInclusion _ H)))=_
    simp_rw [ha.1,ha.2.1,ha.2.2]
    rfl
  have ht := nativeCollarSeries_value_trace u
    (nativeL2ParticularCurve P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val)
    hs.1 hs.2.1 hs.2.2
    (nativeL2ParticularCurve_finite_lift P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val) _ hJ
  have he := congrFun
    (nativeL2ParticularAngular_agrees_continuous P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus H) 0
  simp only [nativeConjugatedCurve,mul_zero,Real.exp_zero,one_smul] at he
  exact ht.trans (congrArg nativeAngularTraceCLM he.symm)

theorem nativePoissonCollarJet_value_trace (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativeCollarValueTraceCLM (nativePoissonCollarJet P b hb)=nativeAngularTraceCLM (P.curve b 0) := by
  let u : AngularIndex → nativeC2OffZero := fun i => ⟨nativePoissonCollarMode P b i,nativePoissonCollarMode_C2 P b i⟩
  have hs := nativePoissonCollar_modes_summable P b hb
  have hf (s : Finset AngularIndex) : cylinderLift (projectedAngular s (nativePoissonReflectedCurve P b))=
      fun x => ∑ i ∈ s,(u i).val x :=
    (nativePoissonReflectedCurve_finite_lift P b s).trans (nativePoissonCollarMode_sum P b s).symm
  have ht := nativeCollarSeries_value_trace u (nativePoissonReflectedCurve P b) hs.1 hs.2.1 hs.2.2
    hf (nativePoissonCollarJet P b hb) rfl
  simpa only [nativePoissonReflectedCurve,if_pos le_rfl] using ht

theorem nativeL2HalfJet_zero_value_trace
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeCollarValueTraceCLM (nativeL2HalfJetCLM P hplus F)=0 := by
  rw [nativeL2HalfJet_eq_difference,map_sub,nativeL2ParticularJet_value_trace,nativePoissonCollarJet_value_trace,
    ← map_sub]
  have h0 := nativeL2HalfCollarCurve_zero P hplus F
  simp only [nativeL2HalfCollarCurve,nativeConjugatedCurve,mul_zero,Real.exp_zero,one_smul,
    nativePoissonReflectedCurve,if_pos le_rfl] at h0
  rw [h0,map_zero]

#print axioms nativeL2ParticularJet_value_trace
#print axioms nativePoissonCollarJet_value_trace
#print axioms nativeL2HalfJet_zero_value_trace
end Yamabe3.Analysis.SpherePolar
