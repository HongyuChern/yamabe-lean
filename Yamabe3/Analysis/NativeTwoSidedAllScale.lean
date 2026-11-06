import Yamabe3.Analysis.NativeTwoSidedNativeAssembly

/-! The same two-source coupled boundary element is used on every inner
scale. The scale-zero jet is exactly the jet already matched to the
inhomogeneous exterior. All scale jets represent one measurable field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1) (t₀ : ℝ)

def nativeTwoSidedAllScaleJetCLM (s : ℝ) : NativeTwoSidedSource →L[ℝ] nativeCollarJetClosure :=
  (nativeFullL2AllScaleJetCLM P hp v hv hb s).comp (ContinuousLinearMap.fst ℝ _ _)+
    nativeBoundaryPoissonJetCLM P hp (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀)
      (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀)
      (exists_nativeTwoSidedSourceSigma_energy P hp v hv hb t₀) s

def nativeTwoSidedAllScaleRawJetCLM (s : ℝ) : NativeTwoSidedSource →L[ℝ] NativeCollarJet :=
  nativeCollarJetClosure.subtypeL.comp (nativeTwoSidedAllScaleJetCLM P hp v hv hb t₀ s)

theorem nativeTwoSidedAllScale_zero (X : NativeTwoSidedSource) :
    nativeTwoSidedAllScaleJetCLM P hp v hv hb t₀ 0 X=nativeTwoSidedInteriorJetCLM P hp v hv hb t₀ X := rfl

theorem nativeTwoSidedAllScale_memH2 (s : ℝ) (X : NativeTwoSidedSource) :
    MemWkp 2 2 (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X).1 nativePoissonEntranceCollar :=
  nativeCollarJetClosure_memH2 (nativeTwoSidedAllScaleJetCLM P hp v hv hb t₀ s X)

theorem nativeTwoSidedAllScale_equation
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    (s : ℝ) (X : NativeTwoSidedSource) :
    nativePositiveScaledRestrictionCLM s
      ((∑j : Fin 3,(nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X).2.2 j j)+
        nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential)
          (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X).1)=
      nativePositiveScaledRestrictionCLM s (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s X.1)) := by
  let H := nativeFullL2AllScaleRawJetCLM P hp v hv hb s X.1
  let b := nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X
  let L := nativeBoundaryPoissonRawJetCLM P hp (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀)
    (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀)
    (exists_nativeTwoSidedSourceSigma_energy P hp v hv hb t₀) s X
  let V := boundedTimeTranslate ℝ s P.potential
  have hh := nativeFullL2AllScale_equation P hp v hv hb hpot s X.1
  have hl := nativePoissonAllScale_homogeneous P hp s b (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀ X)
  change nativePositiveScaledRestrictionCLM s
    ((∑j : Fin 3,(H.2.2 j j+L.2.2 j j))+nativeCollarPotentialMulCLM V (H.1+L.1))=_
  rw [Finset.sum_add_distrib,(nativeCollarPotentialMulCLM V).map_add]
  have he : ((∑j : Fin 3,H.2.2 j j)+(∑j : Fin 3,L.2.2 j j))+
      (nativeCollarPotentialMulCLM V H.1+nativeCollarPotentialMulCLM V L.1)=
      ((∑j : Fin 3,H.2.2 j j)+nativeCollarPotentialMulCLM V H.1)+
      ((∑j : Fin 3,L.2.2 j j)+nativeCollarPotentialMulCLM V L.1) := by abel
  change nativePositiveScaledRestrictionCLM s
    ((∑j : Fin 3,L.2.2 j j)+nativeCollarPotentialMulCLM V L.1)=0 at hl
  rw [he,map_add,hh,hl,add_zero]

theorem nativeTwoSidedAllScale_same_field (X : NativeTwoSidedSource) :
    ∃w : ℝ×S→ℝ,Measurable w ∧ ∀s : ℝ,
      ((nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  obtain ⟨w,hw,hj⟩ := exists_nativeFullL2AllScale_same_field P hp v hv hb X.1
  let b := nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X
  obtain ⟨q,hq,hqa,_⟩ := nativePoissonReflectedCurve_joint_representative P b
  refine ⟨fun p => w p+q p,hw.add hq.measurable,fun s => ?_⟩
  have hl := nativePoissonAllScaleValue_same_field P hp b
    (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀ X) hq.measurable hqa s
  have ha := Lp.coeFn_add (nativeFullL2AllScaleRawJetCLM P hp v hv hb s X.1).1 (nativePoissonAllScaleValue P hp s b)
  filter_upwards [hj s,hl,ha] with x hh hl ha
  change ((nativeFullL2AllScaleRawJetCLM P hp v hv hb s X.1).1+nativePoissonAllScaleValue P hp s b) x=_
  rw [ha]
  change (nativeFullL2AllScaleRawJetCLM P hp v hv hb s X.1).1 x+nativePoissonAllScaleValue P hp s b x=_
  rw [hh,hl,native_cylinderLift_add]
  exact (mul_add _ _ _).symm

theorem exists_nativeTwoSidedAllScale_bound :
    ∃D : ℝ,0<D ∧ ∀s : ℝ,‖nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s‖≤D := by
  obtain ⟨H,hH,hh⟩ := exists_family_nativeFullL2AllScale_bound P.κ_nonneg P.κ_lt_one (norm_nonneg P.potential)
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_nativeBoundaryPoisson_all_scale_bounds P hp
    (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀) (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀)
    (exists_nativeTwoSidedSourceSigma_energy P hp v hv hb t₀)
  let N := ∑k : Fin 3,K k
  have hN : 0≤N := Finset.sum_nonneg (fun k _ => hK k)
  let L := 1+C+G+N
  have hL : 0<L := by dsimp only [L];linarith
  have hCL : C≤L := by dsimp only [L];linarith
  have hGL : G≤L := by dsimp only [L];linarith
  have hNL : N≤L := by dsimp only [L];linarith
  refine ⟨H+L,by positivity,fun s => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun X => ?_)⟩
  let b := nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X
  have ht := h X s
  have h1 : ‖fun j => nativePoissonAllScaleFirst P hp s b j‖≤G*‖X‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr ht.2.1
  have h2 : ‖fun k j => nativePoissonAllScaleSecond P hp s b k j‖≤N*‖X‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    exact (ht.2.2 k j).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ => hK i) (Finset.mem_univ k)) (norm_nonneg X))
  have hJ : ‖(nativePoissonAllScaleValue P hp s b,(fun j => nativePoissonAllScaleFirst P hp s b j),
      (fun k j => nativePoissonAllScaleSecond P hp s b k j))‖≤L*‖X‖ := by
    rw [Prod.norm_def,Prod.norm_def]
    exact max_le (ht.1.trans (mul_le_mul_of_nonneg_right hCL (norm_nonneg X)))
      (max_le (h1.trans (mul_le_mul_of_nonneg_right hGL (norm_nonneg X)))
        (h2.trans (mul_le_mul_of_nonneg_right hNL (norm_nonneg X))))
  have hF := (nativeFullL2AllScaleRawJetCLM P hp v hv hb s).le_of_opNorm_le
    (hh P rfl le_rfl hp v hv hb s) X.1
  have hF' := hF.trans (mul_le_mul_of_nonneg_left (norm_fst_le X) hH.le)
  change ‖nativeFullL2AllScaleRawJetCLM P hp v hv hb s X.1+
    (nativePoissonAllScaleValue P hp s b,(fun j => nativePoissonAllScaleFirst P hp s b j),
      (fun k j => nativePoissonAllScaleSecond P hp s b k j))‖≤_
  exact (norm_add_le _ _).trans ((add_le_add hF' hJ).trans_eq (by ring))

#print axioms nativeTwoSidedAllScale_zero
#print axioms nativeTwoSidedAllScale_memH2
#print axioms nativeTwoSidedAllScale_equation
#print axioms nativeTwoSidedAllScale_same_field
#print axioms exists_nativeTwoSidedAllScale_bound
end Yamabe3.Analysis.SpherePolar
