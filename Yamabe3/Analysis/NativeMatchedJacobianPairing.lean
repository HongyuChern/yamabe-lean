import Yamabe3.Analysis.NativeMatchedShellEquation
import Yamabe3.Analysis.NativeMatchedGeometricSource

/-! The actual native Jacobian on the one full-mode field has its exact
full-source weak pairing on all positive-time spectral tests. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
attribute [local irreducible] nativeMatchedGeometricRowCLM nativeFullShellSourceReturnCLM nativeMatchedGeometricSourceTerm
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (B : NativeHighPotential) (p : DelaunayPhaseData κ)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)

theorem nativeMatchedJacobian_shell_return (g : RiemannianMetric 3 E) (ε : ℝ)
    (n : ℕ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeOrbitCollarJacobianCLM g (ε*Real.exp (-nativeLogShellCenter n)) p.orbit p.smooth p.bounded
        (p.phase+nativeLogShellCenter n) (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp (nativeLogShellCenter n) F))=
    -nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace (nativeLogShellCenter n) F))+
        nativeMatchedGeometricSourceTerm hκ0 hκ1 B p hp g ε n F := by
  let J := nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp (nativeLogShellCenter n) F
  let V := delaunayPhasePotentialBCF p.orbit p.smooth.continuous p.bounded (p.phase+nativeLogShellCenter n)
  change nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
    (-((∑ j : Fin 3,J.2.2 j j)+nativeCollarPotentialMulCLM V J.1)+
      nativeFullCollarJetErrorCLM g (ε*Real.exp (-nativeLogShellCenter n)) p.orbit p.smooth
        (p.phase+nativeLogShellCenter n) J)=_
  rw [map_add,map_neg]
  have h := nativeMatchedDelaunay_shell_equation hκ0 hκ1 B p hp n F
  change nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
    ((∑ j : Fin 3,J.2.2 j j)+nativeCollarPotentialMulCLM V J.1)=_ at h
  rw [h]
  simp only [nativeMatchedGeometricSourceTerm,nativeMatchedGeometricRowCLM,ContinuousLinearMap.comp_apply,J]

private theorem full_operator_inner_hasSum {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (T : ℕ → X →L[ℝ] X) (hs : Summable T) (F G : X) :
    HasSum (fun n => inner ℝ (T n F) G) (inner ℝ ((∑' n,T n) F) G) := by
  let ev := ContinuousLinearMap.apply ℝ X F
  have h : HasSum (fun n => inner ℝ G (T n F)) (inner ℝ G ((∑' n,T n) F)) :=
    (hs.hasSum.mapL ev).mapL (innerSL ℝ G)
  simpa only [real_inner_comm] using h

theorem nativeMatchedGeometricSource_pairing_hasSum
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (F G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    HasSum (fun n => inner ℝ (nativeMatchedGeometricSourceTerm hκ0 hκ1 B p hp (g a) ε n F) G)
      (inner ℝ (nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε F) G) := by
  have hs := nativeMatchedGeometricSourceTerm_summable hκ0 hκ1 B p hp Λ g hB hρ ε hε hε1 a ha
  exact full_operator_inner_hasSum _ hs F G

theorem nativeMatchedJacobian_pairing
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (F G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    HasSum (fun n => inner ℝ
      (nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
        (nativeOrbitCollarJacobianCLM (g a) (ε*Real.exp (-nativeLogShellCenter n)) p.orbit p.smooth p.bounded
          (p.phase+nativeLogShellCenter n) (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp (nativeLogShellCenter n) F))) G)
      (-(∫ t in Ioi 0,inner ℝ (F t) (G t))+
        inner ℝ (nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε F) G) := by
  have h1 := (nativeFullSourceReturn_reconstructs F G).neg
  have h2 := nativeMatchedGeometricSource_pairing_hasSum hκ0 hκ1 B p hp Λ g hB hρ ε hε hε1 a ha F G
  simpa only [nativeMatchedJacobian_shell_return,inner_add_left,inner_neg_left] using h1.add h2

#print axioms nativeMatchedJacobian_shell_return
#print axioms nativeMatchedGeometricSource_pairing_hasSum
#print axioms nativeMatchedJacobian_pairing
end Yamabe3.Analysis.SpherePolar
