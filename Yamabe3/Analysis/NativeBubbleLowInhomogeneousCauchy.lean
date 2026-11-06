import Yamabe3.Analysis.NativeBubbleLowReverseSolver
import Yamabe3.Analysis.NativeLowCauchyBoundedTraces
import Yamabe3.Analysis.NativeLowL2ValueTrace

/-! Actual bounded low-mode exterior Cauchy solver with an L2 source.
The correction is the previously constructed finite compensated field;
its coefficients are outputs, not additional source compatibility inputs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

abbrev NativeLowInhomogeneousData := Lp AngularSpectralSpace 2 (volume : Measure ℝ) × (AngularL2×AngularL2)

def nativeBubbleLowEntranceCLM (t₀ : ℝ) : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] AngularL2 :=
  (BoundedContinuousFunction.evalCLM ℝ 0).comp (nativeLowL2AngularCLM (nativeBubbleReverseProfile t₀)
    (nativeBubbleReverseProfile_continuous t₀) (nativeBubbleReverseProfile_bounds t₀))

def nativeBubbleLowNormalCLM (t₀ : ℝ) : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] AngularL2 :=
  nativeLowReverseL2NormalAngularCLM (nativeBubbleReverseProfile t₀)
    (nativeBubbleReverseProfile_continuous t₀) (nativeBubbleReverseProfile_bounds t₀)

def nativeBubbleLowCorrectionDataCLM (t₀ : ℝ) : NativeLowInhomogeneousData →L[ℝ] (AngularL2×AngularL2) :=
  let f := ContinuousLinearMap.fst ℝ (Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (AngularL2×AngularL2)
  let b := ContinuousLinearMap.snd ℝ (Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (AngularL2×AngularL2)
  let d := (ContinuousLinearMap.fst ℝ AngularL2 AngularL2).comp b-(nativeBubbleLowEntranceCLM t₀).comp f
  let n := (nativeBubbleLowNormalCLM t₀).comp f-(ContinuousLinearMap.snd ℝ AngularL2 AngularL2).comp b-(1/2:ℝ) • d
  d.prod n

def nativeBubbleLowInhomogeneousJetCLM {t₀ : ℝ} (ht : 0<t₀) :
    NativeLowInhomogeneousData →L[ℝ] nativeCollarJetClosure :=
  (nativeBubbleLowReverseJetCLM t₀).comp (ContinuousLinearMap.fst ℝ _ _)+
    (nativeLowCauchyCollarCLM ht).comp (nativeBubbleLowCorrectionDataCLM t₀)

theorem nativeBubbleLowInhomogeneousJetCLM_eq {t₀ : ℝ} (ht : 0<t₀)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) :
    nativeBubbleLowInhomogeneousJetCLM ht (F,(d,n))=nativeBubbleLowReverseJetCLM t₀ F+
      nativeLowCauchyCollarCLM ht
        (d-nativeBubbleLowEntranceCLM t₀ F,nativeBubbleLowNormalCLM t₀ F-n-(1/2:ℝ) • (d-nativeBubbleLowEntranceCLM t₀ F)) := rfl

private theorem entrance_low (t₀ : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowProjection (nativeBubbleLowEntranceCLM t₀ F)=nativeBubbleLowEntranceCLM t₀ F :=
  nativeLowL2_entrance_is_low _ _ _ F

private theorem normal_low (t₀ : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowProjection (nativeBubbleLowNormalCLM t₀ F)=nativeBubbleLowNormalCLM t₀ F := by
  change nativeLowProjection (nativeLowProjection _)=nativeLowProjection _
  classical
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply,nativeLowProjection,nativeAngularProjection_coefficient]
  split_ifs <;> rfl

theorem nativeBubbleLowInhomogeneousJet_traces {t₀ : ℝ} (ht : 0<t₀)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) :
    nativeCollarValueTraceCLM (nativeBubbleLowInhomogeneousJetCLM ht (F,(d,n)))=
      nativeAngularTraceCLM (nativeLowProjection d) ∧
    nativeCollarNormalTraceCLM (nativeBubbleLowInhomogeneousJetCLM ht (F,(d,n)))=
      nativeAngularTraceCLM (nativeLowProjection n) := by
  rw [nativeBubbleLowInhomogeneousJetCLM_eq,map_add,map_add,
    (nativeBubbleLowReverseJet_traces t₀ F).1,(nativeBubbleLowReverseJet_traces t₀ F).2,
    (nativeLowCauchyCollarCLM_traces ht _ _).1,(nativeLowCauchyCollarCLM_traces ht _ _).2]
  change nativeAngularTraceCLM (nativeBubbleLowEntranceCLM t₀ F)+nativeAngularTraceCLM _=_ ∧
    nativeAngularTraceCLM (nativeBubbleLowNormalCLM t₀ F)+nativeAngularTraceCLM _=_
  let a := nativeBubbleLowEntranceCLM t₀ F
  let N := nativeBubbleLowNormalCLM t₀ F
  have ha : a+nativeLowProjection (d-a)=nativeLowProjection d := by
    rw [map_sub,entrance_low];abel
  have hn : N+(-nativeLowProjection (N-n-(1/2:ℝ) • (d-a))-
      (1/2:ℝ) • nativeLowProjection (d-a))=nativeLowProjection n := by
    rw [map_sub,map_sub,map_smul,normal_low]
    abel
  constructor
  · exact (nativeAngularTraceCLM.map_add a (nativeLowProjection (d-a))).symm.trans
      (congrArg (fun b : AngularL2 => nativeAngularTraceCLM b) ha)
  · exact (nativeAngularTraceCLM.map_add N
      (-nativeLowProjection (N-n-(1/2:ℝ) • (d-a))-(1/2:ℝ) • nativeLowProjection (d-a))).symm.trans
      (congrArg (fun b : AngularL2 => nativeAngularTraceCLM b) hn)

def nativeBubbleLowInhomogeneousCompensation {t₀ : ℝ} (ht : 0<t₀)
    (X : NativeLowInhomogeneousData) (i : AngularIndex) : ℝ :=
  let dn := nativeBubbleLowCorrectionDataCLM t₀ X
  bubbleLowCauchyCompensation i t₀ (inner ℝ (angularBasis i) dn.1) (inner ℝ (angularBasis i) dn.2) 0

theorem nativeBubbleLowInhomogeneousJet_source {t₀ : ℝ} (ht : 0<t₀)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) :
    (nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
      (nativeBubbleLowInhomogeneousJetCLM ht (F,(d,n))).val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => -8*(nativeNegativeCollarRestrictionCLM (nativeLowReverseL2SourceCLM F) : E→ℝ) x+
        nativeBubbleCollarCompensation t₀ (nativeBubbleLowInhomogeneousCompensation ht (F,(d,n))) x) := by
  let dn := nativeBubbleLowCorrectionDataCLM t₀ (F,(d,n))
  let c := nativeBubbleLowInhomogeneousCompensation ht (F,(d,n))
  let C := nativeLowCauchyCollarCLM ht dn
  have hc : (nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))) C.val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      nativeBubbleCollarCompensation t₀ c := by
    dsimp only [C]
    rw [nativeLowCauchyCollarCLM_eq]
    exact nativeBubbleLowCollar_source_ae t₀ c _ _ (fun i hi => (nativeLowCauchyQ_spec ht dn.1 dn.2 i hi).2.1)
  change (nativeExteriorModelJacobianCLM _ (nativeBubbleLowReverseJetCLM t₀ F+C).val : E→ℝ)=ᵐ[_] _
  rw [Submodule.coe_add,map_add,nativeBubbleLowReverseJet_equation]
  filter_upwards [Lp.coeFn_add ((-8:ℝ) • nativeNegativeCollarRestrictionCLM (nativeLowReverseL2SourceCLM F))
    (nativeExteriorModelJacobianCLM _ C.val),
    Lp.coeFn_smul (-8:ℝ) (nativeNegativeCollarRestrictionCLM (nativeLowReverseL2SourceCLM F)),hc] with x ha hs hc
  rw [ha]
  simp only [Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hc]
  rfl

#print axioms nativeBubbleLowInhomogeneousJetCLM_eq
#print axioms nativeBubbleLowInhomogeneousJet_traces
#print axioms nativeBubbleLowInhomogeneousJet_source
end Yamabe3.Analysis.SpherePolar
