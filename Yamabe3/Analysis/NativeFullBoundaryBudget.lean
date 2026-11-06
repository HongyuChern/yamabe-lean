import Yamabe3.Analysis.NativeFullSourceBoundaryCorrection
import Yamabe3.Analysis.NativeFamilyPoissonAllScale

/-! The actual coupled boundary correction is a linear map of the same
full source. Its complete Poisson boundary energy has a bound chosen
before both potentials and before the source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

variable (B P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

def nativeFullSourceBoundarySigmaCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] AngularH1 :=
  (nativeHighCoupledDtNInverse B P).comp (-nativeFullL2NormalAngularCLM P hp v hv hb)

theorem nativeFullSourceBoundarySigmaCLM_apply (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeFullSourceBoundarySigmaCLM B P hp v hv hb F=nativeFullSourceBoundarySigma B P hp v hv hb F := rfl

theorem nativeFullSourceBoundary_energy (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativePoissonBoundaryEnergy (nativeFullSourceBoundarySigma B P hp v hv hb F)≤
      8*(∑'i,nativeAngularWeightedSquare (1/2) (nativeFullL2NormalAngularCLM P hp v hv hb F) i) := by
  have hs := nativeFullSourceBoundarySigma_spectral B P hp v hv hb F
  obtain ⟨b,he,hbound⟩ := nativeAngular_three_halves_exists_H1 _ hs.1
  have heq : b=nativeFullSourceBoundarySigma B P hp v hv hb F := angularEmbedding_injective he
  rw [heq] at hbound
  unfold nativePoissonBoundaryEnergy
  linarith only [hbound,hs.2]

omit B P hp v hv hb in
theorem exists_family_nativeFullBoundary_energy {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃C : ℝ,0≤C ∧ ∀(B P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀(hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
        (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
        (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)),
        nativePoissonBoundaryEnergy (nativeFullSourceBoundarySigma B P hp v hv hb F)≤C*‖F‖^2 := by
  obtain ⟨C,hC,h⟩ := exists_family_nativeFullL2_trace_spectral_bounds hκ0 hκ1 hM
  refine ⟨8*C,by positivity,fun B P hP hPM hp v hv hb F => ?_⟩
  have hn := h P hP hPM hp v hv hb F
  have hv0 : 0≤∑'i,nativeAngularWeightedSquare (3/2) (nativeTraceAngularCLM
      (nativeCollarValueTraceCLM (nativeFullL2AllScaleJetCLM P hp v hv hb 0 F))) i :=
    tsum_nonneg (fun _ => sq_nonneg _)
  have hs := nativeFullSourceBoundary_energy B P hp v hv hb F
  linarith only [hn.2.2,hv0,hs]

#print axioms nativeFullSourceBoundarySigmaCLM_apply
#print axioms nativeFullSourceBoundary_energy
#print axioms exists_family_nativeFullBoundary_energy
end Yamabe3.Analysis.SpherePolar
