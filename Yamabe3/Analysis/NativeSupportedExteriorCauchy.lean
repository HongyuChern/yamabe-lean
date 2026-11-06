import Yamabe3.Analysis.NativeBubbleExteriorInhomogeneous
import Yamabe3.Analysis.NativeLowSourceLocality

/-! Support-aware exterior Cauchy producer. Actual low and high traces are
preserved while the same original full source is retained beyond the collar.
The finite compensation is a computed output. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeSupportedLowPhysicalDataCLM (b : ℝ) : NativeLowInhomogeneousData →L[ℝ] NativeLowInhomogeneousData :=
  ((nativeSupportedReverseSourcePrepareCLM b).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.snd ℝ _ _)

def nativeSupportedBubbleLowPhysicalCauchyCLM (b : ℝ) {t₀ : ℝ} (ht : 0<t₀) :
    NativeLowInhomogeneousData →L[ℝ] nativeCollarJetClosure :=
  (nativeBubbleLowInhomogeneousJetCLM ht).comp (nativeSupportedLowPhysicalDataCLM b)

def nativeSupportedBubbleExteriorInhomogeneousJetCLM (b : ℝ) {t₀ : ℝ} (ht : 0<t₀) :
    NativeLowInhomogeneousData →L[ℝ] nativeCollarJetClosure :=
  nativeSupportedBubbleLowPhysicalCauchyCLM b ht+
    (nativeBubbleExteriorHighSourceCLM t₀).comp (ContinuousLinearMap.fst ℝ _ _)

def nativeSupportedBubbleExteriorInhomogeneousCompensation (b : ℝ) {t₀ : ℝ} (ht : 0<t₀)
    (X : NativeLowInhomogeneousData) : AngularIndex→ℝ :=
  nativeBubbleLowInhomogeneousCompensation ht (nativeSupportedLowPhysicalDataCLM b X)

theorem nativeSupportedBubbleExteriorInhomogeneousJet_traces (b : ℝ) {t₀ : ℝ} (ht : 0<t₀)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) :
    nativeCollarValueTraceCLM (nativeSupportedBubbleExteriorInhomogeneousJetCLM b ht (F,(d,n)))=
      nativeAngularTraceCLM (nativeLowProjection d) ∧
    nativeCollarNormalTraceCLM (nativeSupportedBubbleExteriorInhomogeneousJetCLM b ht (F,(d,n)))=
      nativeAngularTraceCLM (nativeLowProjection n+nativeBubbleExteriorHighNormalCLM t₀ F) := by
  change nativeCollarValueTraceCLM (nativeBubbleLowInhomogeneousJetCLM ht
    (nativeSupportedReverseSourcePrepareCLM b F,(d,n))+nativeBubbleExteriorHighSourceCLM t₀ F)=_ ∧
    nativeCollarNormalTraceCLM (nativeBubbleLowInhomogeneousJetCLM ht
      (nativeSupportedReverseSourcePrepareCLM b F,(d,n))+nativeBubbleExteriorHighSourceCLM t₀ F)=_
  rw [map_add,map_add,(nativeBubbleLowInhomogeneousJet_traces ht _ d n).1,
    (nativeBubbleLowInhomogeneousJet_traces ht _ d n).2]
  constructor
  · have hz : nativeCollarValueTraceCLM (nativeBubbleExteriorHighSourceCLM t₀ F)=0 :=
      nativeExteriorL2HighJet_zero_value _ _ _ F
    rw [hz,add_zero]
  · have he : nativeAngularTraceCLM (nativeBubbleExteriorHighNormalCLM t₀ F)=
        nativeCollarNormalTraceCLM (nativeBubbleExteriorHighSourceCLM t₀ F) :=
      nativeTraceAngular_right_inverse _
    rw [←he]
    exact (nativeAngularTraceCLM.map_add _ _).symm

theorem nativeSupportedBubbleExteriorInhomogeneousJet_source (b : ℝ) {t₀ : ℝ} (ht : 0<t₀)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) :
    (nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
      (nativeSupportedBubbleExteriorInhomogeneousJetCLM b ht (F,(d,n))).val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM F) : E→ℝ) x+
        nativeBubbleCollarCompensation t₀ (nativeSupportedBubbleExteriorInhomogeneousCompensation b ht (F,(d,n))) x) := by
  let H := nativeSupportedReverseSourcePrepareCLM b F
  let L := nativeBubbleLowInhomogeneousJetCLM ht (H,(d,n))
  let K := nativeBubbleExteriorHighSourceCLM t₀ F
  let J := nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
  let low := nativeNegativeCollarRestrictionCLM (nativeL2LowPhysicalSourceCLM F)
  let high := nativeNegativeCollarRestrictionCLM (nativeL2HighPhysicalSourceCLM F)
  let full := nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM F)
  have hl := nativeBubbleLowInhomogeneousJet_source ht H d n
  have he : nativeLowReverseL2SourceCLM H=nativeL2LowPhysicalSourceCLM F := nativeSupportedReverseSource_local_reconstruction b F hF
  rw [he] at hl
  have hk : J K.val=(-8:ℝ) • high := nativeExteriorL2HighJet_equation _ _ _
    (nativeBubbleExteriorPotential_eq_phase t₀).symm F
  have hsum : low+high=full := by
    dsimp only [low,high,full]
    rw [←map_add,add_comm,nativeL2High_add_low_source]
  have hsae : ∀ᵐx ∂volume.restrict nativeNegativeEntranceCollar,low x+high x=full x := by
    have hh := Lp.coeFn_add low high
    rw [hsum] at hh
    exact hh.symm
  change (J (L+K).val : E→ℝ)=ᵐ[_] _
  rw [Submodule.coe_add,map_add,hk]
  filter_upwards [Lp.coeFn_add (J L.val) ((-8:ℝ) • high),Lp.coeFn_smul (-8:ℝ) high,hl,hsae] with x ha hs hl hh
  rw [ha]
  change J L.val x+((-8:ℝ) • high) x=_
  rw [hs]
  change J L.val x+(-8)*high x=_
  change J L.val x= -8*low x+nativeBubbleCollarCompensation t₀
    (nativeSupportedBubbleExteriorInhomogeneousCompensation b ht (F,(d,n))) x at hl
  change _= -8*full x+_
  rw [hl,←hh]
  ring

theorem nativeSupportedBubbleExteriorInhomogeneousJet_bound (b : ℝ) {t₀ : ℝ} (ht : 0<t₀) :
    ∃C : ℝ,0<C ∧ ∀ (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2),
      ‖nativeSupportedBubbleExteriorInhomogeneousJetCLM b ht (F,(d,n))‖≤C*max ‖F‖ (max ‖d‖ ‖n‖) := by
  refine ⟨‖nativeSupportedBubbleExteriorInhomogeneousJetCLM b ht‖+1,by positivity,fun F d n => ?_⟩
  have h := (nativeSupportedBubbleExteriorInhomogeneousJetCLM b ht).le_opNorm (F,(d,n))
  simpa only [Prod.norm_def] using h.trans
    (mul_le_mul_of_nonneg_right (by linarith : ‖nativeSupportedBubbleExteriorInhomogeneousJetCLM b ht‖≤
      ‖nativeSupportedBubbleExteriorInhomogeneousJetCLM b ht‖+1) (norm_nonneg (F,(d,n))))

#print axioms nativeSupportedBubbleExteriorInhomogeneousJet_traces
#print axioms nativeSupportedBubbleExteriorInhomogeneousJet_source
#print axioms nativeSupportedBubbleExteriorInhomogeneousJet_bound
end Yamabe3.Analysis.SpherePolar
