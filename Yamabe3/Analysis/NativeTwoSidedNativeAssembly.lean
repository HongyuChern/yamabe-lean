import Yamabe3.Analysis.NativeTwoSidedInteriorNativeEquation

/-! One corrected pair, one coupled boundary element, both actual native
collar equations, both traces and the weak gluing identity. The radius is
chosen after the fixed orbit and positive bubble entrance, before sources.
This is a local collar assembly; it does not assert a global outer inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

/-- All conclusions refer to exactly the same `Y`, inner jet and outer jet. -/
def NativeTwoSidedNativeAssembly (P : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
    {t₀ : ℝ} (ht : 0<t₀) (g : RiemannianMetric 3 E) (r : ℝ)
    (X Y : NativeTwoSidedSource) : Prop :=
  let J := nativeTwoSidedInteriorJetCLM P hp v hv hb t₀ Y
  let K := nativeTwoSidedExteriorJetCLM P hp v hv hb ht Y
  Y=X+nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r Y ∧
  nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K ∧
  nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K ∧
  NativeCollarWeakGluing J K ∧
  nativeInteriorNativeJacobianCLM g r P.potential J.val=
    (-8:ℝ) • nativePositiveCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.1) ∧
  (nativeExteriorNativeJacobianCLM g r (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))) K.val : E→ℝ)
    =ᵐ[volume.restrict nativeNegativeEntranceCollar]
    (fun x => -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2) : E→ℝ) x+
      nativeBubbleCollarCompensation t₀ (nativeTwoSidedExteriorCompensation P hp v hv hb ht Y) x)

theorem exists_nativeTwoSidedNativeAssembly
    (P : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    {t₀ : ℝ} (ht : 0<t₀)
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀p∈Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃r₀ : ℝ,0<r₀ ∧ r₀≤1 ∧ ∀r : ℝ,0≤r → r≤r₀ → ∀p∈Λ,
      ∃T : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource,‖T‖≤2 ∧ ∀X,
        NativeTwoSidedNativeAssembly P hp v hv hb ht (g p) r X (T X) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeTwoSidedCollarSourceError_linear_bound P hp v hv hb ht Λ g hB hρ
  refine ⟨min 1 (1/(2*C)),lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
  intro r hr hr0 p hp'
  have hK : ‖nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht (g p) r‖≤1/2 := by
    apply (hc r hr (hr0.trans (min_le_left _ _)) p hp').trans
    have he := mul_le_mul_of_nonneg_left (hr0.trans (min_le_right _ _)) hC.le
    exact he.trans_eq (by field_simp)
  let K := nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht (g p) r
  refine ⟨nativeTwoSidedFeedbackCLM K hK,nativeTwoSidedFeedback_norm K hK,fun X => ?_⟩
  have hm := nativeTwoSidedSource_actual_matching P hp v hv hb ht (nativeTwoSidedFeedbackCLM K hK X)
  exact ⟨nativeTwoSidedFeedback_fixed K hK X,hm.1,hm.2,
    nativeTwoSidedSource_actual_weak_gluing P hp v hv hb ht _,
    nativeTwoSidedInterior_feedback_native_equation P hp v hv hb hpot ht (g p) r hK X,
    nativeTwoSidedExterior_feedback_native_equation P hp v hv hb ht (g p) r hK X⟩

theorem exists_nativeDelaunayBubble_two_sided_native_assembly
    {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (p : DelaunayPhaseData κ)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
    {t₀ : ℝ} (ht : 0<t₀)
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    let P := p.nativeHighPotential hκ0 hκ1
    let v := fun t => p.orbit (t+p.phase)
    let hv := p.smooth.continuous.comp (continuous_id.add continuous_const)
    let hb := fun t => p.bounded (t+p.phase)
    ∃r₀ : ℝ,0<r₀ ∧ r₀≤1 ∧ ∀r : ℝ,0≤r → r≤r₀ → ∀a∈Λ,
      ∃T : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource,‖T‖≤2 ∧ ∀X,
        NativeTwoSidedNativeAssembly P hp v hv hb ht (g a) r X (T X) := by
  dsimp only
  apply exists_nativeTwoSidedNativeAssembly _ _ _ _ _ _ ht Λ g hB hρ
  apply BoundedContinuousFunction.ext
  intro t
  change (15/4)*p.orbit (t+p.phase)^4=(15/4)*p.orbit (t+0+p.phase)^4
  rw [add_zero]

#print axioms exists_nativeTwoSidedNativeAssembly
#print axioms exists_nativeDelaunayBubble_two_sided_native_assembly
end Yamabe3.Analysis.SpherePolar
