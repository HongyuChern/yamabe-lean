import Yamabe3.Analysis.NativeBubbleLowInhomogeneousCauchy
import Yamabe3.Analysis.NativeLowReverseSourceBinding
import Yamabe3.Analysis.NativeExteriorL2HighNormal

/-! The actual exterior collar solution for the original full L2 source,
with prescribed low value/normal data and zero high value. The low source
preprocessor cancels its radial weight; high and low therefore refer to
one input source. The finite compensation remains explicitly present. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeLowPhysicalDataCLM : NativeLowInhomogeneousData →L[ℝ] NativeLowInhomogeneousData :=
  (nativeLowReverseSourcePrepareCLM.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.snd ℝ _ _)

def nativeBubbleLowPhysicalCauchyCLM {t₀ : ℝ} (ht : 0<t₀) :
    NativeLowInhomogeneousData →L[ℝ] nativeCollarJetClosure :=
  (nativeBubbleLowInhomogeneousJetCLM ht).comp nativeLowPhysicalDataCLM

def nativeBubbleExteriorHighSourceCLM (t₀ : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  nativeExteriorL2HighJetCLM (fullBubbleHighPotential t₀) (fullBubbleHighPotential (-t₀))
    (fullBubblePhasePotential_plus_kernel t₀)

def nativeBubbleExteriorHighNormalCLM (t₀ : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] AngularL2 :=
  nativeExteriorL2HighNormalAngularCLM (fullBubbleHighPotential t₀) (fullBubbleHighPotential (-t₀))
    (fullBubblePhasePotential_plus_kernel t₀)

def nativeBubbleExteriorInhomogeneousJetCLM {t₀ : ℝ} (ht : 0<t₀) :
    NativeLowInhomogeneousData →L[ℝ] nativeCollarJetClosure :=
  nativeBubbleLowPhysicalCauchyCLM ht+
    (nativeBubbleExteriorHighSourceCLM t₀).comp (ContinuousLinearMap.fst ℝ _ _)

def nativeBubbleExteriorInhomogeneousCompensation {t₀ : ℝ} (ht : 0<t₀)
    (X : NativeLowInhomogeneousData) : AngularIndex→ℝ :=
  nativeBubbleLowInhomogeneousCompensation ht (nativeLowPhysicalDataCLM X)

theorem nativeBubbleExteriorInhomogeneousJet_traces {t₀ : ℝ} (ht : 0<t₀)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) :
    nativeCollarValueTraceCLM (nativeBubbleExteriorInhomogeneousJetCLM ht (F,(d,n)))=
      nativeAngularTraceCLM (nativeLowProjection d) ∧
    nativeCollarNormalTraceCLM (nativeBubbleExteriorInhomogeneousJetCLM ht (F,(d,n)))=
      nativeAngularTraceCLM (nativeLowProjection n+nativeBubbleExteriorHighNormalCLM t₀ F) := by
  change nativeCollarValueTraceCLM (nativeBubbleLowInhomogeneousJetCLM ht
    (nativeLowReverseSourcePrepareCLM F,(d,n))+nativeBubbleExteriorHighSourceCLM t₀ F)=_ ∧
    nativeCollarNormalTraceCLM (nativeBubbleLowInhomogeneousJetCLM ht
      (nativeLowReverseSourcePrepareCLM F,(d,n))+nativeBubbleExteriorHighSourceCLM t₀ F)=_
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

theorem nativeBubbleExteriorInhomogeneousJet_source {t₀ : ℝ} (ht : 0<t₀)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) :
    (nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
      (nativeBubbleExteriorInhomogeneousJetCLM ht (F,(d,n))).val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM F) : E→ℝ) x+
        nativeBubbleCollarCompensation t₀ (nativeBubbleExteriorInhomogeneousCompensation ht (F,(d,n))) x) := by
  let H := nativeLowReverseSourcePrepareCLM F
  let L := nativeBubbleLowInhomogeneousJetCLM ht (H,(d,n))
  let K := nativeBubbleExteriorHighSourceCLM t₀ F
  let J := nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
  let low := nativeNegativeCollarRestrictionCLM (nativeL2LowPhysicalSourceCLM F)
  let high := nativeNegativeCollarRestrictionCLM (nativeL2HighPhysicalSourceCLM F)
  let full := nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM F)
  have hl := nativeBubbleLowInhomogeneousJet_source ht H d n
  have he : nativeLowReverseL2SourceCLM H=nativeL2LowPhysicalSourceCLM F := nativeLowReverseSourcePrepare_reconstructs F
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
    (nativeBubbleExteriorInhomogeneousCompensation ht (F,(d,n))) x at hl
  change _= -8*full x+_
  rw [hl,←hh]
  ring

theorem nativeBubbleExteriorInhomogeneousJet_bound {t₀ : ℝ} (ht : 0<t₀) :
    ∃C : ℝ,0<C ∧ ∀ (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2),
      ‖nativeBubbleExteriorInhomogeneousJetCLM ht (F,(d,n))‖≤C*max ‖F‖ (max ‖d‖ ‖n‖) := by
  refine ⟨‖nativeBubbleExteriorInhomogeneousJetCLM ht‖+1,by positivity,fun F d n => ?_⟩
  have h := (nativeBubbleExteriorInhomogeneousJetCLM ht).le_opNorm (F,(d,n))
  simpa only [Prod.norm_def] using h.trans
    (mul_le_mul_of_nonneg_right (by linarith : ‖nativeBubbleExteriorInhomogeneousJetCLM ht‖≤
      ‖nativeBubbleExteriorInhomogeneousJetCLM ht‖+1) (norm_nonneg (F,(d,n))))

#print axioms nativeBubbleExteriorInhomogeneousJet_traces
#print axioms nativeBubbleExteriorInhomogeneousJet_source
#print axioms nativeBubbleExteriorInhomogeneousJet_bound
end Yamabe3.Analysis.SpherePolar
