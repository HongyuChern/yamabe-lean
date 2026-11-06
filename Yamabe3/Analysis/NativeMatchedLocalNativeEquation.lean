import Yamabe3.Analysis.NativeWeakJacobianLocality

/-! The same feedback field solves the actual weak native equation on
every physical scale window inside the punctured ball. The local H2
regularity and all source identities are produced together. -/
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

theorem exists_uniform_nativeMatchedFeedback_local_native_equation
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
          MemLp (nativePhysicalWeakJacobian (g a) ε p.orbit p.phase (cylinderLift w)) 2
            (volume.restrict (Metric.ball 0 1 \ {(0:E)})) ∧
          (∀s : ℝ,MemWkp 2 2 (cylinderLift w) (nativePhysicalScaleWindow s) ∧
            nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) (g a) ε p.orbit p.phase (cylinderLift w)
              =ᵐ[volume.restrict (nativePhysicalScaleWindow s∩(Metric.ball 0 1 \ {(0:E)}))]
                (fun x => -nativeFullPhysicalSourceRepresentative f x)) := by
  obtain ⟨ε₀,hε₀,hε1,h⟩ := exists_uniform_nativeMatchedFeedback_physical_ae hκ0 hκ1 Λ g hB hρ
  refine ⟨ε₀,hε₀,hε1,fun B p hp ε hε hε0 a ha => ?_⟩
  obtain ⟨T,hT,hf⟩ := h B p hp ε hε hε0 a ha
  refine ⟨T,hT,fun f => ?_⟩
  obtain ⟨hfix,w,hw,hlocal,hjet,hm,heq⟩ := hf f
  have hbind := nativeMatchedPhysicalJacobian_same_weak_operator hκ0 hκ1 B p hp (g a) ε (T f)
    (fun s => (hjet s).1)
  have hwin (s : ℝ) : MemWkp 2 2 (cylinderLift w) (nativePhysicalScaleWindow s) :=
    native_scaled_H2_to_physical s ((MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) (hjet s).1).mp (hjet s).2)
  refine ⟨hfix,w,hw,hlocal,hjet,hm.ae_eq hbind,fun s => ⟨hwin s,?_⟩⟩
  have hsrc := hbind.symm.trans heq
  have hpatch := nativePhysicalWeakJacobian_local (nativePhysicalScaleWindow_open s) (hwin s)
    (fun n => hwin (nativeLogShellCenter n)) (g a) ε p.orbit p.phase
  exact hpatch.symm.trans (ae_mono (Measure.restrict_mono inter_subset_right le_rfl) hsrc)

#print axioms exists_uniform_nativeMatchedFeedback_local_native_equation
end Yamabe3.Analysis.SpherePolar
