import Yamabe3.Analysis.NativeFullBoundaryAllScale

/-! One linear source operator includes both the full-mode particular
solution and its actual coupled boundary correction at every scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

 theorem exists_family_nativeFullBoundaryPoisson_raw_jet_bound {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ L : ℝ,0<L ∧ ∀ (B P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
        (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1) (s : ℝ),
        ‖nativeFullBoundaryPoissonRawJetCLM B P hp v hv hb s‖≤L := by
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_family_nativeFullBoundaryPoisson_H2_bounds hκ0 hκ1 hM
  let N := ∑ k : Fin 3,K k
  have hN : 0≤N := Finset.sum_nonneg (fun k _ => hK k)
  let L := 1+C+G+N
  have hL : 0<L := by dsimp only [L];linarith
  have hCL : C≤L := by dsimp only [L];linarith
  have hGL : G≤L := by dsimp only [L];linarith
  have hNL : N≤L := by dsimp only [L];linarith
  refine ⟨L,hL,fun B P hP hPM hp v hv hb s => ContinuousLinearMap.opNorm_le_bound _ hL.le (fun F => ?_)⟩
  let b := nativeFullSourceBoundarySigma B P hp v hv hb F
  have ht := h B P hP hPM hp v hv hb F s
  have h1 : ‖fun j => nativePoissonAllScaleFirst P hp s b j‖≤G*‖F‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr ht.2.1
  have h2 : ‖fun k j => nativePoissonAllScaleSecond P hp s b k j‖≤N*‖F‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    exact (ht.2.2 k j).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ => hK i) (Finset.mem_univ k)) (norm_nonneg F))
  change ‖(nativePoissonAllScaleValue P hp s b,(fun j => nativePoissonAllScaleFirst P hp s b j),
    (fun k j => nativePoissonAllScaleSecond P hp s b k j))‖≤L*‖F‖
  rw [Prod.norm_def,Prod.norm_def]
  exact max_le (ht.1.trans (mul_le_mul_of_nonneg_right hCL (norm_nonneg F)))
    (max_le (h1.trans (mul_le_mul_of_nonneg_right hGL (norm_nonneg F)))
      (h2.trans (mul_le_mul_of_nonneg_right hNL (norm_nonneg F))))

variable (B P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

def nativeFullMatchedAllScaleRawJetCLM (s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  nativeFullL2AllScaleRawJetCLM P hp v hv hb s+nativeFullBoundaryPoissonRawJetCLM B P hp v hv hb s

def nativeFullMatchedAllScaleJetCLM (s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  nativeFullL2AllScaleJetCLM P hp v hv hb s+nativeFullBoundaryPoissonJetCLM B P hp v hv hb s

theorem nativeFullMatchedAllScale_zero (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeFullMatchedAllScaleJetCLM B P hp v hv hb 0 F=nativeFullSourceMatchedInteriorJet B P hp v hv hb F := by
  change nativeFullL2AllScaleJetCLM P hp v hv hb 0 F+nativeFullBoundaryPoissonJetCLM B P hp v hv hb 0 F=_
  rw [nativeFullBoundaryPoisson_zero]
  rfl

theorem nativeFullMatchedAllScale_memH2 (s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeFullMatchedAllScaleRawJetCLM B P hp v hv hb s F).1 nativePoissonEntranceCollar :=
  nativeCollarJetClosure_memH2 (nativeFullMatchedAllScaleJetCLM B P hp v hv hb s F)

theorem nativeFullMatchedAllScale_equation
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    (s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativePositiveScaledRestrictionCLM s
      ((∑ j : Fin 3,(nativeFullMatchedAllScaleRawJetCLM B P hp v hv hb s F).2.2 j j)+
        nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential)
          (nativeFullMatchedAllScaleRawJetCLM B P hp v hv hb s F).1)=
      nativePositiveScaledRestrictionCLM s (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F)) := by
  let H := nativeFullL2AllScaleRawJetCLM P hp v hv hb s F
  let L := nativeFullBoundaryPoissonRawJetCLM B P hp v hv hb s F
  let V := boundedTimeTranslate ℝ s P.potential
  have hh := nativeFullL2AllScale_equation P hp v hv hb hpot s F
  have hl := nativePoissonAllScale_homogeneous P hp s (nativeFullSourceBoundarySigma B P hp v hv hb F)
    (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1
  change nativePositiveScaledRestrictionCLM s
    ((∑ j : Fin 3,(H.2.2 j j+L.2.2 j j))+nativeCollarPotentialMulCLM V (H.1+L.1))=_
  rw [Finset.sum_add_distrib,(nativeCollarPotentialMulCLM V).map_add]
  have he : ((∑ j : Fin 3,H.2.2 j j)+(∑ j : Fin 3,L.2.2 j j))+
      (nativeCollarPotentialMulCLM V H.1+nativeCollarPotentialMulCLM V L.1)=
      ((∑ j : Fin 3,H.2.2 j j)+nativeCollarPotentialMulCLM V H.1)+
        ((∑ j : Fin 3,L.2.2 j j)+nativeCollarPotentialMulCLM V L.1) := by abel
  change nativePositiveScaledRestrictionCLM s
    ((∑ j : Fin 3,L.2.2 j j)+nativeCollarPotentialMulCLM V L.1)=0 at hl
  rw [he,map_add,hh,hl,add_zero]

theorem exists_nativeFullMatchedAllScale_same_field (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ∃ w : ℝ × S → ℝ,Measurable w ∧ ∀ s : ℝ,
      ((nativeFullMatchedAllScaleRawJetCLM B P hp v hv hb s F).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  obtain ⟨w,hw,hj⟩ := exists_nativeFullL2AllScale_same_field P hp v hv hb F
  let b := nativeFullSourceBoundarySigma B P hp v hv hb F
  obtain ⟨q,hq,hqa,_⟩ := nativePoissonReflectedCurve_joint_representative P b
  refine ⟨fun p => w p+q p,hw.add hq.measurable,fun s => ?_⟩
  have hl := nativePoissonAllScaleValue_same_field P hp b
    (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1 hq.measurable hqa s
  have ha := Lp.coeFn_add (nativeFullL2AllScaleRawJetCLM P hp v hv hb s F).1 (nativePoissonAllScaleValue P hp s b)
  filter_upwards [hj s,hl,ha] with x hh hl ha
  change ((nativeFullL2AllScaleRawJetCLM P hp v hv hb s F).1+nativePoissonAllScaleValue P hp s b) x=_
  rw [ha]
  change (nativeFullL2AllScaleRawJetCLM P hp v hv hb s F).1 x+nativePoissonAllScaleValue P hp s b x=_
  rw [hh,hl,native_cylinderLift_add]
  exact (mul_add _ _ _).symm

omit B P hp v hv hb in
theorem exists_family_nativeFullMatchedAllScale_bound {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ L : ℝ,0<L ∧ ∀ (B P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
        (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1) (s : ℝ),
        ‖nativeFullMatchedAllScaleRawJetCLM B P hp v hv hb s‖≤L := by
  obtain ⟨H,hH,hh⟩ := exists_family_nativeFullL2AllScale_bound hκ0 hκ1 hM
  obtain ⟨L,hL,hl⟩ := exists_family_nativeFullBoundaryPoisson_raw_jet_bound hκ0 hκ1 hM
  exact ⟨H+L,by positivity,fun B P hP hPM hp v hv hb s =>
    (norm_add_le _ _).trans (add_le_add (hh P hP hPM hp v hv hb s) (hl B P hP hPM hp v hv hb s))⟩

#print axioms exists_family_nativeFullBoundaryPoisson_raw_jet_bound
#print axioms nativeFullMatchedAllScale_zero
#print axioms nativeFullMatchedAllScale_memH2
#print axioms nativeFullMatchedAllScale_equation
#print axioms exists_nativeFullMatchedAllScale_same_field
#print axioms exists_family_nativeFullMatchedAllScale_bound
end Yamabe3.Analysis.SpherePolar
