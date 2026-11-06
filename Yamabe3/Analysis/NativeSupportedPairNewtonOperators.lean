import Yamabe3.Analysis.NativeSupportedSourcePairSpace
import Yamabe3.Analysis.NativeSupportedOuterNewtonAnnulus
import Yamabe3.Analysis.NativeH4CollarRealization
import Yamabe3.Analysis.NativeCollarJetValueInjective

/-! The actual Newton gain is a bounded operator estimate on the complete
supported SAME source-pair space. The all-scale jet is identified with
the same annular field by volume-class injectivity, not by a new choice. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
variable (P:NativeHighPotential)
  (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)

 theorem exists_nativeSupportedPair_Newton_jet_bound :
    ∃S C:ℝ,S ≤ -(1/2:ℝ) ∧ 0 ≤ C ∧ ∀X:nativeSupportedSourcePairSpace b,∀s:ℝ,s ≤ S →
      ‖nativeSupportedOuterAllScaleJet b ht X.val.2
        (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
        (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val)
        (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X.val) s‖ ≤
          C*Real.exp (5*s/2)*‖X‖ := by
  obtain ⟨S,hS,D,hD,hd⟩:=exists_nativeSupportedOuter_same_field_Newton_annulus_H4 b ht
  let A:=nativeTwoSidedExteriorDataCLM P hp v hv hb
  let Sig:=nativeTwoSidedSourceSigmaCLM P hp v hv hb τ
  let C:=D.toReal*(‖A‖+‖Sig‖)
  refine ⟨S,C,hS,by dsimp only [C];positivity,?_⟩
  intro X s hs
  have hF:∀ᵐt:ℝ∂volume,t < b → X.val.2 t=0 :=
    (nativeSupportedSourcePairSpace_mem_iff b X.val).mp X.property
  obtain ⟨w,hw,hl,ha,hj,hreg⟩:=hd X.val.2
    (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
    (Sig X.val) (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X.val) hF
  let u:=weightedPhysicalDilation s (cylinderLift w)
  let J:=nativeSupportedOuterAllScaleJet b ht X.val.2
    (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
    (Sig X.val) (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X.val) s
  have hu:MemWkp 4 2 u halfEndBasicAnnulus := (hreg s hs).1
  obtain ⟨K,hKv,hK⟩:=exists_nativeCollarJet_of_weak_H4 hu
  have he:J=K := nativeCollarJet_value_injective (Lp.ext ((hj s).trans hKv.symm))
  have hn:‖J‖ ≤ (iteratedWeakSobolevNorm 4 2 u halfEndBasicAnnulus).toReal := by rw [he];exact hK
  have hh:=ENNReal.toReal_mono (ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top) ((hreg s hs).2 4 le_rfl)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hh
  have hbnd:‖A X.val‖+‖Sig X.val‖ ≤ (‖A‖+‖Sig‖)*‖X‖ :=
    (add_le_add (A.le_opNorm X.val) (Sig.le_opNorm X.val)).trans_eq (by
      change ‖A‖*‖X.val‖+‖Sig‖*‖X.val‖=(‖A‖+‖Sig‖)*‖X.val‖
      ring)
  apply (hn.trans hh).trans
  change D.toReal*(Real.exp (5*s/2)*(‖A X.val‖+‖Sig X.val‖)) ≤ _
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbnd (Real.exp_pos _).le) ENNReal.toReal_nonneg).trans_eq (by dsimp only [C];ring)

theorem exists_nativeSupportedPair_Newton_all_scale_CLM :
    ∃S C:ℝ,S ≤ -(1/2:ℝ) ∧ 0 ≤ C ∧ ∀s:ℝ,s ≤ S →
      ∃J:nativeSupportedSourcePairSpace b →L[ℝ] nativeCollarJetClosure,
        ‖J‖ ≤ C*Real.exp (5*s/2) ∧ ∀X,
          J X=nativeSupportedOuterAllScaleJet b ht X.val.2
            (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
            (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val)
            (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X.val) s := by
  obtain ⟨S,C,hS,hC,hbnd⟩:=exists_nativeSupportedPair_Newton_jet_bound P hp v hv hb b ht
  obtain ⟨D,hD,hd⟩:=exists_nativeSupportedTwoSided_all_scale_CLM P hp v hv hb b ht
  refine ⟨S,C,hS,hC,fun s hs=>?_⟩
  obtain ⟨J,hJ,hJv⟩:=hd s (hs.trans (by linarith only [hS]))
  let T:=J.comp (nativeSupportedSourcePairSpace b).subtypeL
  refine ⟨T,T.opNorm_le_bound (by positivity) ?_,fun X=>hJv X.val⟩
  intro X
  change ‖J X.val‖ ≤ _
  rw [hJv]
  exact hbnd X s hs

#print axioms exists_nativeSupportedPair_Newton_jet_bound
#print axioms exists_nativeSupportedPair_Newton_all_scale_CLM
end Yamabe3.Analysis.SpherePolar
