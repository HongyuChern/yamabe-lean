import Yamabe3.Analysis.NativeSpectralJetMatching
import Yamabe3.Analysis.NativeOrbitCollarJacobian
import Yamabe3.Analysis.NativeExteriorModelJacobian

/-! The boundary correction preserves the actual inner model source.
The outer source is the computed finite compensation. These are identities
of the actual collar operators, with the physical factor eight retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeCauchyCompensationData {τ : ℝ} (ht : 0<τ) (D N : AngularL2) (i : AngularIndex) : ℝ :=
  bubbleLowCauchyCompensation i τ (inner ℝ (angularBasis i) D)
    (inner ℝ (angularBasis i) (-N-(1/2:ℝ) • D)) 0

theorem nativePoissonAddition_preserves_source (P : NativeHighPotential) (J : nativeCollarJetClosure)
    (σ : AngularH1) (hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ)) :
    nativePositiveCollarRestrictionCLM (nativeFlatCollarJetCLM P.potential (J+nativePoissonCollarJet P σ hσ).val)=
      nativePositiveCollarRestrictionCLM (nativeFlatCollarJetCLM P.potential J.val) := by
  have hz : nativePositiveCollarRestrictionCLM
      (nativeFlatCollarJetCLM P.potential (nativePoissonCollarJet P σ hσ).val)=0 := by
    change nativePositiveCollarRestrictionCLM
      (-((∑j : Fin 3,nativePoissonCollarSecond P σ j j)+
        nativeCollarPotentialMulCLM P.potential (nativePoissonCollarValue P σ)))=0
    rw [map_neg,nativePoissonCollar_homogeneous P σ hσ,neg_zero]
  rw [Submodule.coe_add,map_add,map_add,hz,add_zero]

theorem nativeC2PoissonAddition_classical_source (P : NativeHighPotential) (u : nativeC2OffZero)
    (σ : AngularH1) (hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ)) :
    (nativePositiveCollarRestrictionCLM
      (nativeFlatCollarJetCLM P.potential (nativeC2CollarJetInclusion u+nativePoissonCollarJet P σ hσ).val) : E→ℝ)
      =ᵐ[volume.restrict nativePositiveEntranceCollar]
      (fun x => -nativeCoordinateLaplacian u.val x-nativeHalfEndPotentialCoefficient P.potential x*u.val x) := by
  rw [nativePoissonAddition_preserves_source]
  exact (nativePositiveCollarRestrictionCLM_ae _).trans
    (ae_mono (Measure.restrict_mono inter_subset_left le_rfl) (nativeFlatCollarJet_C2_ae P.potential u))

theorem nativeCauchyOuter_computed_source {τ : ℝ} (ht : 0<τ) (D N : AngularL2)
    (β : AngularH1) (hβ : NativeAngularSpectralRegular (3/2) (angularEmbedding β)) :
    let B := fullBubbleHighPotential (-τ)
    let Ko := nativeLowCauchyCollarCLM ht (D,-N-(1/2:ℝ) • D)+nativePoissonExteriorCollarJet B β hβ
    (nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential B) Ko.val : E→ℝ)
      =ᵐ[volume.restrict nativeNegativeEntranceCollar] nativeBubbleCollarCompensation τ (nativeCauchyCompensationData ht D N) := by
  dsimp only
  rw [nativeLowCauchyCollarCLM_eq]
  exact nativeBubbleHighLowCollar_same_source τ (nativeCauchyCompensationData ht D N)
    (nativeLowCauchyQ ht (nativeLowCauchyCoordinateCLM (D,-N-(1/2:ℝ) • D)))
    (nativeLowCauchyQ_C2 ht _) (fun i hi => (nativeLowCauchyQ_spec ht D (-N-(1/2:ℝ) • D) i hi).2.1) β hβ

#print axioms nativePoissonAddition_preserves_source
#print axioms nativeC2PoissonAddition_classical_source
#print axioms nativeCauchyOuter_computed_source
end Yamabe3.Analysis.SpherePolar
