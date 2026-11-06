import Yamabe3.Analysis.NativeFullSourceActualMatching
import Yamabe3.Analysis.NativeBubbleHighLowIdentity
import Yamabe3.Analysis.NativeFullNativeGreen

/-! One same-source construction has genuine H2 collars, the exterior
compensating physical equation, both traces, and native Green boundary
cancellation for a common Gauss metric. The native PDE residual still
requires geometric feedback; this lemma does not erase that residual. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativeMatchedCollars_native_green_cancel (J K : nativeCollarJetClosure)
    (hn : nativeCollarNormalTraceCLM K=nativeCollarNormalTraceCLM J)
    (g : RiemannianMetric 3 E) (hg : ∀x z : E,g.inner x x z=inner ℝ x z)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) :
    8*nativeCollarGreenRegionCLM (ball 0 1) isOpen_ball.measurableSet g ψ hψ J.val+
      8*nativeCollarGreenVolumeCLM g ψ hψ K.val=0 := by
  rw [nativeCollarWeakGreen_interior g hg ψ hψ hc hs J,nativeCollarWeakGreen g hg ψ hψ hc hs K]
  have he : nativeCollarNativeNormalPairCLM g ψ hψ.continuous K=
      nativeCollarNativeNormalPairCLM g ψ hψ.continuous J := by
    change inner ℝ (nativeSphereWeightedTest g ψ hψ.continuous) (nativeCollarNormalTraceCLM K)=_
    rw [hn]
    rfl
  rw [he]
  ring

variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

theorem exists_nativeFullSource_model_boundary_assembly
    {t₀ : ℝ} (ht : 0<t₀) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    let B := fullBubbleHighPotential (-t₀)
    let σ := nativeFullSourceBoundarySigma B P hp v hv hb F
    let J := nativeFullSourceMatchedInteriorJet B P hp v hv hb F
    let d := nativeLowL2AngularCLM v hv hb F 0
    let N := nativeFullL2NormalAngularCLM P hp v hv hb F
    ∃ (c : AngularIndex → ℝ) (q : AngularIndex → ℝ → ℝ)
      (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i)),
      (∀i∈nativeLowIndexFinset,
        c i=bubbleLowCauchyCompensation i t₀ (inner ℝ (angularBasis i) d)
          (inner ℝ (angularBasis i) (-N-(1/2:ℝ) • d)) 0 ∧
        (∀t,deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t= -c i*bubbleCompensation i t) ∧
        Tendsto (q i) atBot (𝓝 0) ∧ Tendsto (deriv (q i)) atBot (𝓝 0)) ∧
      let K := nativeBubbleLowCollarJet t₀ q hq+
        nativePoissonExteriorCollarJet B σ (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1
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
  dsimp only
  obtain ⟨c,q,hq,hcomp,hJ,hK,hval,hn⟩ := exists_nativeFullSource_actual_H2_collar_matching P hp v hv hb ht F
  refine ⟨c,q,hq,hcomp,hJ,hK,hval,hn,?_,?_,?_⟩
  · exact nativeBubbleHighLowCollar_same_source t₀ c q hq (fun i hi => (hcomp i hi).2.1) _ _
  · exact exists_nativeBubbleHighLow_same_physical_field t₀ q hq _ _
  · intro g hg ψ hψ hc hs
    exact nativeMatchedCollars_native_green_cancel _ _ hn g hg ψ hψ hc hs

#print axioms nativeMatchedCollars_native_green_cancel
#print axioms exists_nativeFullSource_model_boundary_assembly
end Yamabe3.Analysis.SpherePolar
