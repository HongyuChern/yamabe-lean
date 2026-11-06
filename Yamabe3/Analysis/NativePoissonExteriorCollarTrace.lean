import Yamabe3.Analysis.NativePoissonExteriorFiniteTrace
import Yamabe3.Analysis.NativeL2HalfNormalTrace

/-! Actual exterior entrance traces: reversing cylinder time changes
only the first derivative. The physical conformal half-weight remains. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
theorem nativePoissonExteriorRawJet_mem (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    (nativePoissonExteriorCollarValue P b,nativePoissonExteriorCollarFirst P b,nativePoissonExteriorCollarSecond P b) ∈ nativeCollarJetClosure := by
  let u : AngularIndex → nativeC2OffZero := fun i => ⟨nativePoissonExteriorCollarMode P b i,nativePoissonExteriorCollarMode_C2 P b i⟩
  have hs := nativePoissonExteriorCollar_modes_summable P b hb
  exact nativeCollarJet_series_mem u hs.1 hs.2.1 hs.2.2

def nativePoissonExteriorCollarJet (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) : nativeCollarJetClosure :=
  ⟨(nativePoissonExteriorCollarValue P b,nativePoissonExteriorCollarFirst P b,nativePoissonExteriorCollarSecond P b),nativePoissonExteriorRawJet_mem P b hb⟩

theorem nativePoissonExteriorCollarJet_value_trace (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativeCollarValueTraceCLM (nativePoissonExteriorCollarJet P b hb)=nativeAngularTraceCLM (P.curve b 0) := by
  let u : AngularIndex → nativeC2OffZero := fun i => ⟨nativePoissonExteriorCollarMode P b i,nativePoissonExteriorCollarMode_C2 P b i⟩
  have hs := nativePoissonExteriorCollar_modes_summable P b hb
  have hf (s : Finset AngularIndex) : cylinderLift (projectedAngular s (nativePoissonExteriorCurve P b))=
      fun x => ∑ i ∈ s,(u i).val x :=
    (nativePoissonExteriorCurve_finite_lift P b s).trans (nativePoissonExteriorCollarMode_sum P b s).symm
  have ht := nativeCollarSeries_value_trace u (nativePoissonExteriorCurve P b) hs.1 hs.2.1 hs.2.2
    hf (nativePoissonExteriorCollarJet P b hb) rfl
  simpa only [nativePoissonExteriorCurve,nativePoissonReflectedCurve,neg_zero,if_pos le_rfl] using ht

theorem nativePoissonExteriorCollarJet_normal_trace (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativeCollarNormalTraceCLM (nativePoissonExteriorCollarJet P b hb)=
      nativeAngularTraceCLM (nativePoissonExteriorPhysicalEntranceNormal P b) := by
  let u : AngularIndex → nativeC2OffZero := fun i => ⟨nativePoissonExteriorCollarMode P b i,nativePoissonExteriorCollarMode_C2 P b i⟩
  have hs := nativePoissonExteriorCollar_modes_summable P b hb
  apply nativeCollarNormalTrace_of_C2_limit (l := atTop) (fun s : Finset AngularIndex => ∑ i ∈ s,u i)
    (nativePoissonExteriorCollarJet P b hb)
  · exact nativeC2CollarJet_series_tendsto u hs.1 hs.2.1 hs.2.2
  · have ht := nativeAngularTraceCLM.continuous.continuousAt.tendsto.comp
      (finiteHilbertProjection_tendsto_filter angularBasis tendsto_id (nativePoissonExteriorPhysicalEntranceNormal P b))
    apply ht.congr'
    apply Eventually.of_forall
    intro s
    symm
    apply Lp.ext
    filter_upwards [nativeC2NormalTraceLinear_ae (∑ i ∈ s,u i),
      nativePoissonExteriorFiniteCollar_normal_trace_ae P b s,
      nativeAngularTraceCLM_ae (finiteHilbertProjection angularBasis s (nativePoissonExteriorPhysicalEntranceNormal P b))] with θ hu hp hm
    simp only [Function.comp_apply,id_eq]
    rw [hu,hm]
    have he : (∑ i ∈ s,u i).val=nativePoissonExteriorFiniteCollar P b s := by
      funext x
      simpa only [Submodule.coe_sum,Finset.sum_apply] using congrFun (nativePoissonExteriorCollarMode_sum P b s) x
    rw [he]
    exact hp

#print axioms nativePoissonExteriorRawJet_mem
#print axioms nativePoissonExteriorCollarJet_value_trace
#print axioms nativePoissonExteriorCollarJet_normal_trace
end Yamabe3.Analysis.SpherePolar
