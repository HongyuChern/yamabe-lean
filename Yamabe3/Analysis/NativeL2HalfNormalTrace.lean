import Yamabe3.Analysis.NativeL2HalfValueTrace
import Yamabe3.Analysis.NativePoissonNormalEntrance

/-! The actual radial derivative trace of the same H2 collar is a bounded
operator of the all-L2 source. The Poisson contribution is identified with
the original DtN datum including the physical conformal half-weight. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeC2NormalTraceLinear_ae (u : nativeC2OffZero) :
    (nativeC2NormalTraceLinear u : S → ℝ)=ᵐ[angularVolume]
      (fun θ : S => fderiv ℝ u.val (θ:E) (θ:E)) :=
  (native_C1_sphere_normal_memLp (u.property.of_le (by norm_num))).coeFn_toLp

theorem nativePoissonCollarJet_normal_trace (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativeCollarNormalTraceCLM (nativePoissonCollarJet P b hb)=
      nativeAngularTraceCLM (nativePoissonPhysicalEntranceNormal P b) := by
  let u : AngularIndex → nativeC2OffZero := fun i => ⟨nativePoissonCollarMode P b i,nativePoissonCollarMode_C2 P b i⟩
  have hs := nativePoissonCollar_modes_summable P b hb
  apply nativeCollarNormalTrace_of_C2_limit (l := atTop) (fun s : Finset AngularIndex => ∑ i ∈ s,u i)
    (nativePoissonCollarJet P b hb)
  · exact nativeC2CollarJet_series_tendsto u hs.1 hs.2.1 hs.2.2
  · have ht := nativeAngularTraceCLM.continuous.continuousAt.tendsto.comp
      (finiteHilbertProjection_tendsto_filter angularBasis tendsto_id (nativePoissonPhysicalEntranceNormal P b))
    apply ht.congr'
    apply Eventually.of_forall
    intro s
    symm
    apply Lp.ext
    filter_upwards [nativeC2NormalTraceLinear_ae (∑ i ∈ s,u i),
      nativePoissonFiniteCollar_normal_trace_ae P b s,
      nativeAngularTraceCLM_ae (finiteHilbertProjection angularBasis s (nativePoissonPhysicalEntranceNormal P b))] with θ hu hp hm
    simp only [Function.comp_apply,id_eq]
    rw [hu,hm]
    have he : (∑ i ∈ s,u i).val=nativePoissonFiniteCollar P b s := by
      funext x
      simpa only [Submodule.coe_sum,Finset.sum_apply] using congrFun (nativePoissonCollarMode_sum P b s) x
    rw [he]
    exact hp

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

def nativeL2HalfNormalTraceCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 angularVolume :=
  nativeCollarNormalTraceCLM.comp (nativeL2HalfJetCLM P hplus)

theorem nativeL2HalfNormalTrace_difference
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfNormalTraceCLM P hplus F=
      nativeCollarNormalTraceCLM (nativeL2ParticularJetCLM P hplus F)-
        nativeAngularTraceCLM (nativePoissonPhysicalEntranceNormal P (nativeL2HalfEntrance P hplus F)) := by
  change nativeCollarNormalTraceCLM (nativeL2HalfJetCLM P hplus F)=_
  rw [nativeL2HalfJet_eq_difference,map_sub,nativePoissonCollarJet_normal_trace]

theorem nativeL2HalfNormalTrace_uniform_bound :
    ∃ C : ℝ,0≤C ∧ ∀ F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ),
      ‖nativeL2HalfNormalTraceCLM P hplus F‖≤C*‖F‖ :=
  ⟨‖nativeL2HalfNormalTraceCLM P hplus‖,norm_nonneg _,(nativeL2HalfNormalTraceCLM P hplus).le_opNorm⟩

#print axioms nativePoissonCollarJet_normal_trace
#print axioms nativeL2HalfNormalTrace_difference
#print axioms nativeL2HalfNormalTrace_uniform_bound
end Yamabe3.Analysis.SpherePolar
