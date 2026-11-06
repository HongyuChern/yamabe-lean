import Yamabe3.Analysis.NativeMatchedPhysicalWeakTests
import Yamabe3.Analysis.NativeMatchedJacobianRowBound
import Yamabe3.Analysis.NativePhysicalTestUniqueness

/-! The same feedback field has one square-integrable physical operator
representative. All smooth physical tests identify it with the negative
original source, with the normalization and volume measure unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
attribute [local irreducible] nativeOrbitCollarJacobianCLM
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1)

def nativeMatchedPhysicalJacobian (B : NativeHighPotential) (p : DelaunayPhaseData κ)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
    (g : RiemannianMetric 3 E) (ε : ℝ) (F : NativeSpectralSourceL2) : E → ℝ :=
  nativePhysicalShellAssembly (fun n =>
    nativeOrbitCollarJacobianCLM g (ε*Real.exp (-nativeLogShellCenter n)) p.orbit p.smooth p.bounded
      (p.phase+nativeLogShellCenter n)
      (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp (nativeLogShellCenter n) F))

theorem exists_uniform_nativeMatchedFeedback_physical_ae
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
          MemLp (nativeMatchedPhysicalJacobian hκ0 hκ1 B p hp (g a) ε (T f)) 2
            (volume.restrict (Metric.ball 0 1 \ {(0:E)})) ∧
          nativeMatchedPhysicalJacobian hκ0 hκ1 B p hp (g a) ε (T f)
            =ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})]
              (fun x => -nativeFullPhysicalSourceRepresentative f x) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_nativeMatchedJacobianRow_bound hκ0 hκ1 Λ g hB hρ
  obtain ⟨ε₀,hε₀,hε1,h⟩ := exists_uniform_nativeMatchedFeedback_physical_tests hκ0 hκ1 Λ g hB hρ
  refine ⟨ε₀,hε₀,hε1,fun B p hp ε hε hε0 a ha => ?_⟩
  obtain ⟨T,hT,hf⟩ := h B p hp ε hε hε0 a ha
  refine ⟨T,hT,fun f => ?_⟩
  obtain ⟨hfix,w,hw,hlocal,hjet,htest⟩ := hf f
  let U (n : ℕ) := nativeOrbitCollarJacobianCLM (g a) (ε*Real.exp (-nativeLogShellCenter n))
    p.orbit p.smooth p.bounded (p.phase+nativeLogShellCenter n)
    (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp (nativeLogShellCenter n) (T f))
  have hU (n : ℕ) : ‖U n‖≤C*‖T f‖ := hbound B p hp ε hε (hε0.trans hε1) a ha
    (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n) (T f)
  have hnonneg : 0≤C*‖T f‖ := mul_nonneg hC.le (norm_nonneg _)
  have hm := nativePhysicalShellAssembly_memLp U hnonneg hU
  refine ⟨hfix,w,hw,hlocal,hjet,hm,?_⟩
  apply nativePhysicalTest_ae_eq_negative hm (nativeFullPhysicalSource_memLp f)
  intro φ hφ hc hs
  exact (nativePhysicalShellAssembly_test_hasSum U hnonneg hU φ hφ.continuous hc).unique
    (htest φ hφ hc hs).2

#print axioms exists_uniform_nativeMatchedFeedback_physical_ae
end Yamabe3.Analysis.SpherePolar
