import Yamabe3.Analysis.NativeGlobalGeometricSource

/-! The global source return retains its true shell-by-shell physical
pairing. This is an operator identity, without a pointwise trace assertion. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
attribute [local irreducible] nativeL2HalfGeometricRowCLM nativeShellSourceReturnCLM

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)

theorem nativeGlobalGeometricSource_pairing
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (p : ι) (hp : p∈Λ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    (hvb : ∀ t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2)
    (hvo : ∀ t,deriv (deriv v) t=radialForce (v t)) (phase : ℝ)
    (F G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    inner ℝ (nativeGlobalGeometricSourceCLM P hplus (g p) ε v hv phase F) G =
      ∑' n,∫ x in nativePoissonEntranceCollar,nativeShellSourceWeight x*
        (nativeL2HalfGeometricRowCLM P hplus (g p) ε v hv phase (nativeLogShellCenter n) F : E → ℝ) x*
        (nativeL2HighPhysicalSourceCLM
          (l2TimeTranslateCLM (SpectralSpace AngularIndex) (nativeLogShellCenter n) G) : E → ℝ) x := by
  have hs := nativeGeometricSourceTerm_summable P hplus Λ g hB hρ ε hε hε1 p hp v hv hvb hvo phase
  let ev := ContinuousLinearMap.apply ℝ (Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) F
  have hsum : nativeGlobalGeometricSourceCLM P hplus (g p) ε v hv phase F=
      ∑' n,nativeGeometricSourceTerm P hplus (g p) ε v hv phase n F := ev.map_tsum hs
  rw [hsum,real_inner_comm]
  change (innerSL ℝ G) (∑' n,nativeGeometricSourceTerm P hplus (g p) ε v hv phase n F)=_
  have hsF : Summable (fun n => nativeGeometricSourceTerm P hplus (g p) ε v hv phase n F) := ev.summable hs
  rw [(innerSL ℝ G).map_tsum hsF]
  apply tsum_congr
  intro n
  change inner ℝ G (nativeGeometricSourceTerm P hplus (g p) ε v hv phase n F)=_
  rw [real_inner_comm]
  simpa only [nativeGeometricSourceTerm,ContinuousLinearMap.comp_apply] using
    nativeShellSourceReturn_pairing (nativeLogShellCenter n)
      (nativeL2HalfGeometricRowCLM P hplus (g p) ε v hv phase (nativeLogShellCenter n) F) G

#print axioms nativeGlobalGeometricSource_pairing
end Yamabe3.Analysis.SpherePolar
