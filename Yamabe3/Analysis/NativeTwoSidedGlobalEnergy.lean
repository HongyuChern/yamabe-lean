import Yamabe3.Analysis.NativeMatchedGlobalEnergy
import Yamabe3.Analysis.NativeTwoSidedAllScale
import Yamabe3.Analysis.NativeSupportedTwoSidedAllScaleOperators
import Yamabe3.Analysis.NativeSupportedTwoSidedExteriorField

/-! ACTUAL coupled-model global energy producer. All intermediate
all-scale jet, norm and interface certificates are discharged by the
existing same-source model producers. The resulting field is one
element of the original H1 completion, not a family chosen per test. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD

theorem exists_nativeTwoSided_global_energy_family
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1)) (N:ℕ) :
    ∃L:NativeTwoSidedSource →L[ℝ] H1Zero Deuc univ,
      ∀X:NativeTwoSidedSource,∃wi wo:ℝ×S→ℝ,Measurable wi ∧ Measurable wo ∧
        (∀s:ℝ,NativeScaledJetRep (nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s X) s wi) ∧
        (∀s:ℝ,NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X s) s wo) ∧
        (toL2 Deuc univ (L X):E→ℝ)=ᵐ[volume]
          fun y=>nativeOuterCollarCutoff χ (N+1) y*(ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wo) y := by
  let Wi:NativeTwoSidedSource→ℝ×S→ℝ:=fun X=>(nativeTwoSidedAllScale_same_field P hp v hv hb τ X).choose
  have hWi (X:NativeTwoSidedSource):Measurable (Wi X) ∧ ∀s:ℝ,
      NativeScaledJetRep (nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s X) s (Wi X) :=
    (nativeTwoSidedAllScale_same_field P hp v hv hb τ X).choose_spec
  let Wo:NativeTwoSidedSource→ℝ×S→ℝ:=fun X=>
    (exists_nativeSupportedOuter_same_field_all_scale b ht X.2
      (nativeLowL2AngularCLM v hv hb X.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.1)
      (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X) (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X)).choose
  have hWo (X:NativeTwoSidedSource):Measurable (Wo X) ∧
      Poincare.Analysis.Elliptic.MemWkpLocally 2 (cylinderLift (Wo X)) ({0}ᶜ:Set E) ∧
      ∀s:ℝ,NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X s) s (Wo X) ∧
        Poincare.Analysis.Sobolev.Euclidean.MemWkp 2 2
          (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X s).val.1 nativePoissonEntranceCollar :=
    (exists_nativeSupportedOuter_same_field_all_scale b ht X.2
      (nativeLowL2AngularCLM v hv hb X.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.1)
      (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X) (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X)).choose_spec
  obtain ⟨C,hC,hCJ⟩:=exists_nativeTwoSidedAllScale_bound P hp v hv hb τ
  let J:ℕ→NativeTwoSidedSource →L[ℝ] nativeCollarJetClosure:=
    fun n=>nativeTwoSidedAllScaleJetCLM P hp v hv hb τ (((n+1:ℕ):ℝ)/4)
  have hJ (n:ℕ):‖J n‖ ≤ C := by
    apply (J n).opNorm_le_bound hC.le
    intro X
    change ‖nativeTwoSidedAllScaleRawJetCLM P hp v hv hb τ (((n+1:ℕ):ℝ)/4) X‖ ≤ C*‖X‖
    exact (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb τ _).le_of_opNorm_le (hCJ _) X
  obtain ⟨D,hD,hK⟩:=exists_nativeSupportedTwoSided_all_scale_CLM P hp v hv hb b ht
  have hneg (i:Fin N):-((i.val+2:ℕ):ℝ)/4 ≤ 0 := by
    have hi:0 ≤ (i.val:ℝ) := Nat.cast_nonneg _
    push_cast
    linarith
  let K:Fin N→NativeTwoSidedSource →L[ℝ] nativeCollarJetClosure:=
    fun i=>(hK (-((i.val+2:ℕ):ℝ)/4) (hneg i)).choose
  have hKv (i:Fin N) (X:NativeTwoSidedSource):
      K i X=nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X (-((i.val+2:ℕ):ℝ)/4) :=
    (hK _ (hneg i)).choose_spec.2 X
  let Ji:=nativeTwoSidedInteriorJetCLM P hp v hv hb τ
  let Ko:=nativeSupportedTwoSidedExteriorJetCLM P hp v hv hb b ht
  have hi0 (X:NativeTwoSidedSource):((Ji X).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]cylinderLift (Wi X) := by
    have hh:NativeScaledJetRep (Ji X) 0 (Wi X) := (hWi X).2 0
    simpa only [NativeScaledJetRep,mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul] using hh
  have ho0 (X:NativeTwoSidedSource):((Ko X).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]cylinderLift (Wo X) := by
    have hh:NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X 0) 0 (Wo X) :=
      ((hWo X).2.2 0).1
    rw [nativeSupportedTwoSidedExteriorAllScale_zero_eq] at hh
    dsimp only [Ko]
    simpa only [NativeScaledJetRep,mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul] using hh
  have hvv (X:NativeTwoSidedSource):nativeCollarValueTraceCLM (Ji X)=nativeCollarValueTraceCLM (Ko X) :=
    (nativeSupportedTwoSidedSource_actual_matching P hp v hv hb b ht X).1
  have hi (n:ℕ) (X:NativeTwoSidedSource):((J n X).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>Real.exp (3*(((n+1:ℕ):ℝ)/4)/2)*cylinderLift (Wi X) (Real.exp (-(((n+1:ℕ):ℝ)/4)) • y) := (hWi X).2 _
  have ho (i:Fin N) (X:NativeTwoSidedSource):((K i X).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>Real.exp (3*(-((i.val+2:ℕ):ℝ)/4)/2)*cylinderLift (Wo X) (Real.exp (-(-((i.val+2:ℕ):ℝ)/4)) • y) := by
    rw [hKv]
    exact ((hWo X).2.2 _).1
  obtain ⟨L,hL⟩:=exists_nativeMatched_global_energy_family χ hχ hc hs h1 N J K Ji Ko hC.le hJ hvv
    (fun X=>cylinderLift (Wi X)) (fun X=>cylinderLift (Wo X)) hi0 ho0 hi ho
  exact ⟨L,fun X=>⟨Wi X,Wo X,(hWi X).1,(hWo X).1,(hWi X).2,fun s=>((hWo X).2.2 s).1,hL X⟩⟩

#print axioms exists_nativeTwoSided_global_energy_family
end Yamabe3.Analysis.SpherePolar
