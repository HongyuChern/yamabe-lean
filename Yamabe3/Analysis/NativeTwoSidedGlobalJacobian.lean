import Yamabe3.Analysis.NativeTwoSidedGlobalSource
import Yamabe3.Analysis.NativeFullShellEquation

/-! Exact global positive-time source pairing for the same two-sided
field. Shell weights and the full low-mode source are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
attribute [local irreducible] nativeFullShellSourceReturnCLM nativeTwoSidedGeometricSourceTerm
private theorem operator_inner_hasSum {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (T : ℕ → X →L[ℝ] Y) (hs : Summable T) (F : X) (G : Y) :
    HasSum (fun n => inner ℝ (T n F) G) (inner ℝ ((∑'n,T n) F) G) := by
  let ev := ContinuousLinearMap.apply ℝ Y F
  have h : HasSum (fun n => inner ℝ G (T n F)) (inner ℝ G ((∑'n,T n) F)) :=
    (hs.hasSum.mapL ev).mapL (innerSL ℝ G)
  simpa only [real_inner_comm] using h

variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1) (t₀ : ℝ)

def nativeTwoSidedJacobianRowCLM (g : RiemannianMetric 3 E) (ε s : ℝ) :
    NativeTwoSidedSource →L[ℝ] NativeCollarL2 :=
  ((nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s P.potential)).comp
    (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s))+
    nativeTwoSidedGeometricRowCLM P hp v hv hb t₀ g ε s

theorem nativeTwoSidedJacobian_shell_return
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    (g : RiemannianMetric 3 E) (ε : ℝ) (n : ℕ) (X : NativeTwoSidedSource) :
    nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeTwoSidedJacobianRowCLM P hp v hv hb t₀ g ε (nativeLogShellCenter n) X)=
      -nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
        (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace (nativeLogShellCenter n) X.1))+
        nativeTwoSidedGeometricSourceTerm P hp v hv hb t₀ g ε n X := by
  let J := nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ (nativeLogShellCenter n) X
  let V := boundedTimeTranslate ℝ (nativeLogShellCenter n) P.potential
  change nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
    (-((∑j : Fin 3,J.2.2 j j)+nativeCollarPotentialMulCLM V J.1)+
      nativeTwoSidedGeometricRowCLM P hp v hv hb t₀ g ε (nativeLogShellCenter n) X)=_
  rw [map_add,map_neg]
  have he := nativeFullShellSourceReturn_eq_of_positiveRestriction n _ _
    (nativeTwoSidedAllScale_equation P hp v hv hb t₀ hpot (nativeLogShellCenter n) X)
  change nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
    ((∑j : Fin 3,J.2.2 j j)+nativeCollarPotentialMulCLM V J.1)=_ at he
  rw [he]
  simp only [nativeTwoSidedGeometricSourceTerm,ContinuousLinearMap.comp_apply]

theorem nativeTwoSidedGeometricSource_pairing_hasSum
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (X : NativeTwoSidedSource) (G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    HasSum (fun n => inner ℝ (nativeTwoSidedGeometricSourceTerm P hp v hv hb t₀ (g a) ε n X) G)
      (inner ℝ (nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb t₀ (g a) ε X) G) := by
  have hs := nativeTwoSidedGeometricSourceTerm_summable P hp v hv hb t₀ Λ g hB hρ ε hε hε1 a ha
  exact operator_inner_hasSum _ hs X G

theorem nativeTwoSidedJacobian_pairing
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (X : NativeTwoSidedSource) (G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    HasSum (fun n => inner ℝ (nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeTwoSidedJacobianRowCLM P hp v hv hb t₀ (g a) ε (nativeLogShellCenter n) X)) G)
      (-(∫t in Ioi 0,inner ℝ (X.1 t) (G t))+
        inner ℝ (nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb t₀ (g a) ε X) G) := by
  have h1 := (nativeFullSourceReturn_reconstructs X.1 G).neg
  have h2 := nativeTwoSidedGeometricSource_pairing_hasSum P hp v hv hb t₀ Λ g hB hρ ε hε hε1 a ha X G
  simpa only [nativeTwoSidedJacobian_shell_return P hp v hv hb t₀ hpot,inner_add_left,inner_neg_left] using h1.add h2

#print axioms nativeTwoSidedJacobian_shell_return
#print axioms nativeTwoSidedGeometricSource_pairing_hasSum
#print axioms nativeTwoSidedJacobian_pairing
end Yamabe3.Analysis.SpherePolar
