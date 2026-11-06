import Yamabe3.Analysis.NativeMatchedFeedbackField
import Yamabe3.Analysis.NativePhysicalSourceDuality
import Yamabe3.Analysis.NativeAllScaleLocalH2

/-! The same constructed source-feedback field satisfies every compact
physical test in the punctured ball, expressed as the convergent sum of
actual native Jacobian volume rows. This is not yet the exterior equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
attribute [local irreducible] nativeFullShellSourceReturnCLM nativeOrbitCollarJacobianCLM
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1)

theorem exists_uniform_nativeMatchedFeedback_physical_tests
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    ∃ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ (B : NativeHighPotential) (p : DelaunayPhaseData κ)
      (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ),
      ∀ε : ℝ,0≤ε → ε≤ε₀ → ∀a∈Λ,
      ∃T : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2,‖T‖≤2 ∧ ∀f,
        T f=f+nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε (T f) ∧
        ∃w : ℝ × S → ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) ∧
          (∀s : ℝ,((nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s (T f)).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
            (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) ∧
            MemWkp 2 2 (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s (T f)).1 nativePoissonEntranceCollar) ∧
          ∀ (φ : E → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
            tsupport φ⊆Metric.ball 0 1 \ {(0:E)} →
            IntegrableOn (fun x => nativeFullPhysicalSourceRepresentative f x*φ x) (Metric.ball 0 1 \ {(0:E)}) ∧
            HasSum (fun n => Real.exp (-5*nativeLogShellCenter n/2)*
              (∫x in nativeSourceShell,
                (nativeOrbitCollarJacobianCLM (g a) (ε*Real.exp (-nativeLogShellCenter n)) p.orbit p.smooth p.bounded
                  (p.phase+nativeLogShellCenter n)
                  (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp (nativeLogShellCenter n) (T f)) : E → ℝ) x*
                  φ (Real.exp (-nativeLogShellCenter n) • x)))
              (-(∫x in Metric.ball 0 1 \ {(0:E)},nativeFullPhysicalSourceRepresentative f x*φ x)) := by
  obtain ⟨ε₀,hε₀,hε1,h⟩ := exists_uniform_nativeMatchedFeedback_same_field hκ0 hκ1 Λ g hB hρ
  refine ⟨ε₀,hε₀,hε1,fun B p hp ε hε hε0 a ha => ?_⟩
  obtain ⟨T,hT,hf⟩ := h B p hp ε hε hε0 a ha
  refine ⟨T,hT,fun f => ?_⟩
  obtain ⟨hfix,w,hw,hjet,heq⟩ := hf f
  have hlocal : MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) :=
    native_all_scale_H2_local (fun s =>
      (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) (hjet s).1).mp (hjet s).2)
  refine ⟨hfix,w,hw,hlocal,hjet,fun φ hφ hc hs => ?_⟩
  have h0 : (0:E)∉tsupport φ := fun h => (hs h).2 (by simp)
  let G := nativePhysicalPairTestL2 φ hφ hc h0
  have hsum := heq G (nativePhysicalPairTestL2_positive φ hφ hc h0 hs)
  have hsource := nativeFullPhysicalSource_physical_test_pairing_on_ball f φ hφ hc h0 hs
  refine ⟨hsource.1,?_⟩
  change HasSum _ (-inner ℝ f (nativePhysicalPairTestL2 φ hφ hc h0)) at hsum
  rw [hsource.2] at hsum
  simpa only [G,nativeFullShellSourceReturn_physical_test] using hsum

#print axioms exists_uniform_nativeMatchedFeedback_physical_tests
end Yamabe3.Analysis.SpherePolar
