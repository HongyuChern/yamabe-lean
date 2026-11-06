import Yamabe3.Analysis.NativeMatchedLocalNativeEquation
import Yamabe3.Analysis.NativeFullSourceModelBoundaryAssembly

/-! One fixed-point source produces the actual local weak native equation,
its coupled boundary correction and exterior compensated H2 collar.
The shared jet, value and normal trace identities are all joint outputs.
Exterior native geometric/global residuals remain explicit obligations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
attribute [local irreducible] nativeFullShellSourceReturnCLM nativeOrbitCollarJacobianCLM
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1)

theorem exists_uniform_nativeMatchedNative_boundary_assembly
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ (p : DelaunayPhaseData κ)
      (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ),
      ∀t₀ : ℝ,0<t₀ → ∀ε : ℝ,0≤ε → ε≤ε₀ → ∀a∈Λ,
      let B := fullBubbleHighPotential (-t₀)
      let P := p.nativeHighPotential hκ0 hκ1
      let v := fun t => p.orbit (t+p.phase)
      let hv := p.smooth.continuous.comp (continuous_id.add continuous_const)
      let hb := fun t => p.bounded (t+p.phase)
      ∃T : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2,‖T‖≤2 ∧ ∀f,
        T f=f+nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε (T f) ∧
        (∃w : ℝ × S → ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) ∧
          (∀s : ℝ,((nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s (T f)).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
            (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) ∧
            MemWkp 2 2 (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s (T f)).1 nativePoissonEntranceCollar) ∧
          MemLp (nativePhysicalWeakJacobian (g a) ε p.orbit p.phase (cylinderLift w)) 2
            (volume.restrict (Metric.ball 0 1 \ {(0:E)})) ∧
          (∀s : ℝ,MemWkp 2 2 (cylinderLift w) (nativePhysicalScaleWindow s) ∧
            nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) (g a) ε p.orbit p.phase (cylinderLift w)
              =ᵐ[volume.restrict (nativePhysicalScaleWindow s∩(Metric.ball 0 1 \ {(0:E)}))]
                (fun x => -nativeFullPhysicalSourceRepresentative f x))) ∧
        nativeMatchedDelaunayJetCLM hκ0 hκ1 B p hp 0 (T f)=nativeFullSourceMatchedInteriorJet B P hp v hv hb (T f) ∧
        let σ := nativeFullSourceBoundarySigma B P hp v hv hb (T f)
        let J := nativeFullSourceMatchedInteriorJet B P hp v hv hb (T f)
        let d := nativeLowL2AngularCLM v hv hb (T f) 0
        let N := nativeFullL2NormalAngularCLM P hp v hv hb (T f)
    ∃ (c : AngularIndex → ℝ) (q : AngularIndex → ℝ → ℝ)
      (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i)),
      (∀i∈nativeLowIndexFinset,
        c i=bubbleLowCauchyCompensation i t₀ (inner ℝ (angularBasis i) d)
          (inner ℝ (angularBasis i) (-N-(1/2:ℝ) • d)) 0 ∧
        (∀t,deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t= -c i*bubbleCompensation i t) ∧
        Tendsto (q i) atBot (𝓝 0) ∧ Tendsto (deriv (q i)) atBot (𝓝 0)) ∧
      let K := nativeBubbleLowCollarJet t₀ q hq+
        nativePoissonExteriorCollarJet B σ (nativeFullSourceBoundarySigma_spectral B P hp v hv hb (T f)).1
      MemWkp 2 2 (J.val.1 : E → ℝ) nativePoissonEntranceCollar ∧
      MemWkp 2 2 (K.val.1 : E → ℝ) nativePoissonEntranceCollar ∧
      nativeCollarValueTraceCLM K=nativeCollarValueTraceCLM J ∧
      nativeCollarNormalTraceCLM K=nativeCollarNormalTraceCLM J ∧
      (nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential B) K.val : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
        nativeBubbleCollarCompensation t₀ c ∧
      (∃w : ℝ × S → ℝ,StronglyMeasurable w ∧
        (∀t,t≤0 → (fun θ => w (t,θ))=ᵐ[angularVolume] (B.curve σ (-t) : S → ℝ)) ∧
        (K.val.1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
          (fun x => finitePhysical nativeLowIndexFinset (fun i t => q i (t₀+t)) x+cylinderLift w x)) ∧
      ∀ (g : RiemannianMetric 3 E),(∀x z : E,g.inner x x z=inner ℝ x z) →
        ∀ (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ),HasCompactSupport ψ → tsupport ψ⊆nativePoissonEntranceCollar →
          8*nativeCollarGreenRegionCLM (ball 0 1) isOpen_ball.measurableSet g ψ hψ J.val+
            8*nativeCollarGreenVolumeCLM g ψ hψ K.val=0 := by
  obtain ⟨ε₀,hε₀,hε1,h⟩ := exists_uniform_nativeMatchedFeedback_local_native_equation hκ0 hκ1 Λ g hB hρ
  refine ⟨ε₀,hε₀,hε1,?_⟩
  intro p hp t₀ ht ε hε hε0 a ha
  dsimp only
  obtain ⟨T,hT,hf⟩ := h (fullBubbleHighPotential (-t₀)) p hp ε hε hε0 a ha
  refine ⟨T,hT,fun f => ⟨(hf f).1,(hf f).2,?_,?_⟩⟩
  · exact nativeFullMatchedAllScale_zero _ _ _ _ _ _ _
  · exact exists_nativeFullSource_model_boundary_assembly _ _ _ _ _ ht (T f)

#print axioms exists_uniform_nativeMatchedNative_boundary_assembly
end Yamabe3.Analysis.SpherePolar
