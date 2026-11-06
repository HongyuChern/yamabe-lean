import Yamabe3.Analysis.NativeMatchedGeometricFeedback
import Yamabe3.Analysis.NativeMatchedJacobianPairing

/-! One full source fixed point gives one physical H2 field and the
actual native Jacobian equation on every positive-time L2 test.
The actual coupled boundary correction is included before computing the residual. Its low entrance is retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
attribute [local irreducible] nativeMatchedGeometricRowCLM nativeFullShellSourceReturnCLM
  nativeMatchedGlobalGeometricSourceCLM nativeOrbitCollarJacobianCLM
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1)

theorem exists_uniform_nativeMatchedFeedback_same_field
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ (B : NativeHighPotential) (p : DelaunayPhaseData κ)
      (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ),
      ∀ ε : ℝ,0 ≤ ε → ε ≤ ε₀ → ∀ a ∈ Λ, 
      ∃ T : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2,‖T‖≤2 ∧
      ∀ f : NativeSpectralSourceL2,
        T f=f+nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε (T f) ∧
        ∃ w : ℝ × S → ℝ,Measurable w ∧
          (∀ s : ℝ,
            ((nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s (T f)).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
              (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) ∧
            MemWkp 2 2 (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s (T f)).1 nativePoissonEntranceCollar) ∧
          ∀ G : NativeSpectralSourceL2,
            (∀ᵐ t : ℝ ∂volume,t≤0 → G t=0) →
            HasSum (fun n => inner ℝ
              (nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
                (nativeOrbitCollarJacobianCLM (g a) (ε*Real.exp (-nativeLogShellCenter n)) p.orbit p.smooth p.bounded
                  (p.phase+nativeLogShellCenter n)
                  (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp (nativeLogShellCenter n) (T f)))) G)
              (-inner ℝ f G) := by
  obtain ⟨ε₀,hε₀,hε1,h⟩ := exists_uniform_nativeMatchedGeometricSource_feedback hκ0 hκ1 Λ g hB hρ
  refine ⟨ε₀,hε₀,hε1,fun B p hp ε hε hε0 a ha => ?_⟩
  obtain ⟨T,hT,hfix,_⟩ := h B p hp ε hε hε0 a ha
  refine ⟨T,hT,fun f => ?_⟩
  obtain ⟨w,hw,hjet⟩ := nativeMatchedDelaunay_same_field hκ0 hκ1 B p hp (T f)
  refine ⟨hfix f,w,hw,fun s => ⟨hjet s,nativeMatchedDelaunay_memH2 hκ0 hκ1 B p hp s (T f)⟩,fun G hG0 => ?_⟩
  have hsum := nativeMatchedJacobian_pairing hκ0 hκ1 B p hp Λ g hB hρ ε hε (hε0.trans hε1) a ha (T f) G
  have he : -(∫ t in Ioi 0,inner ℝ ((T f) t) (G t))+
      inner ℝ (nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε (T f)) G= -inner ℝ f G := by
    rw [←nativeFullPositiveTest_pairing (T f) G hG0]
    have hi := congrArg (fun Z : NativeSpectralSourceL2 => inner ℝ Z G) (hfix f)
    rw [inner_add_left] at hi
    linarith only [hi]
  rwa [he] at hsum

#print axioms exists_uniform_nativeMatchedFeedback_same_field
end Yamabe3.Analysis.SpherePolar
