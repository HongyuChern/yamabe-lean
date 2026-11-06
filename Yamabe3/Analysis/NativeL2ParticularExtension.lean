import Yamabe3.Analysis.NativeL2ParticularLinear

/-! Actual bounded linear extension of the same physical collar jets to
all L2 sources. The extension agrees on the dense original source space;
closed weak-derivative graphs bind all extended jets to one value. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

private theorem norm_le_sqrt_mul_of_square {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (x : X) (y : Y) {C : ℝ} (hC : 0≤C) (h : ‖y‖^2≤C*‖x‖^2) : ‖y‖≤Real.sqrt C*‖x‖ := by
  have hs : (Real.sqrt C*‖x‖)^2=C*‖x‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  have hn : 0≤Real.sqrt C*‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg y]

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)

theorem nativeL2ParticularLinear_bounds :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0≤C ∧ 0≤G ∧ (∀ k,0≤K k) ∧
      ∀ F : continuousL2Source (SpectralSpace AngularIndex),
      ‖nativeL2ParticularValueLinear hκ0 hκ1 V hminus hplus F‖≤C*‖continuousL2SourceInclusion _ F‖ ∧
      (∀ j,‖nativeL2ParticularFirstLinear hκ0 hκ1 V hminus hplus j F‖≤G*‖continuousL2SourceInclusion _ F‖) ∧
      (∀ k j,‖nativeL2ParticularSecondLinear hκ0 hκ1 V hminus hplus k j F‖≤K k*‖continuousL2SourceInclusion _ F‖) := by
  obtain ⟨C,G,K,hC,hG,hK,he⟩ := exists_nativeL2Particular_H2_norm_bounds hκ0 hκ1 V hminus hplus
  refine ⟨Real.sqrt C,Real.sqrt G,fun k => Real.sqrt (K k),Real.sqrt_nonneg _,Real.sqrt_nonneg _,
    fun k => Real.sqrt_nonneg _,?_⟩
  intro F
  have h := he F.val F.property
  exact ⟨norm_le_sqrt_mul_of_square _ _ hC h.1,fun j => norm_le_sqrt_mul_of_square _ _ hG (h.2.1 j),
    fun k j => norm_le_sqrt_mul_of_square _ _ (hK k) (h.2.2 k j)⟩

def nativeL2ParticularValueCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativeL2ParticularValueLinear hκ0 hκ1 V hminus hplus).extendOfNorm
    (continuousL2SourceInclusion (SpectralSpace AngularIndex))
def nativeL2ParticularFirstCLM (j : Fin 3) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativeL2ParticularFirstLinear hκ0 hκ1 V hminus hplus j).extendOfNorm
    (continuousL2SourceInclusion (SpectralSpace AngularIndex))
def nativeL2ParticularSecondCLM (k j : Fin 3) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativeL2ParticularSecondLinear hκ0 hκ1 V hminus hplus k j).extendOfNorm
    (continuousL2SourceInclusion (SpectralSpace AngularIndex))

theorem nativeL2ParticularCLM_agrees_continuous (F : continuousL2Source (SpectralSpace AngularIndex)) :
    nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus (continuousL2SourceInclusion _ F)=
      nativeL2ParticularValueLinear hκ0 hκ1 V hminus hplus F ∧
    (∀ j,nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus j (continuousL2SourceInclusion _ F)=
      nativeL2ParticularFirstLinear hκ0 hκ1 V hminus hplus j F) ∧
    (∀ k j,nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus k j (continuousL2SourceInclusion _ F)=
      nativeL2ParticularSecondLinear hκ0 hκ1 V hminus hplus k j F) := by
  obtain ⟨C,G,K,_,_,_,hb⟩ := nativeL2ParticularLinear_bounds hκ0 hκ1 V hminus hplus
  exact ⟨LinearMap.extendOfNorm_eq (continuousL2SourceInclusion_dense _) ⟨C,fun F => (hb F).1⟩ F,
    fun j => LinearMap.extendOfNorm_eq (continuousL2SourceInclusion_dense _) ⟨G,fun F => (hb F).2.1 j⟩ F,
    fun k j => LinearMap.extendOfNorm_eq (continuousL2SourceInclusion_dense _) ⟨K k,fun F => (hb F).2.2 k j⟩ F⟩

theorem nativeL2ParticularCLM_weak_jets
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    (∀ j,HasWeakPartialDeriv j (nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus j F)
      (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F) nativePoissonEntranceCollar) ∧
    (∀ k j,HasWeakPartialDeriv k (nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus k j F)
      (nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus j F) nativePoissonEntranceCollar) := by
  constructor
  · intro j
    have hc := (native_weakPartial_Lp_graph_closed (Ω := nativePoissonEntranceCollar) j).preimage
      ((nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus).continuous.prodMk
        (nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus j).continuous)
    refine (continuousL2SourceInclusion_dense (SpectralSpace AngularIndex)).induction_on F hc ?_
    intro H
    have ha := nativeL2ParticularCLM_agrees_continuous hκ0 hκ1 V hminus hplus H
    change HasWeakPartialDeriv j _ _ _
    rw [ha.1,ha.2.1 j]
    exact (nativeL2ParticularCollar_H2_and_jets hκ0 hκ1 V hminus hplus H.val H.property).2.1 j
  · intro k j
    have hc := (native_weakPartial_Lp_graph_closed (Ω := nativePoissonEntranceCollar) k).preimage
      ((nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus j).continuous.prodMk
        (nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus k j).continuous)
    refine (continuousL2SourceInclusion_dense (SpectralSpace AngularIndex)).induction_on F hc ?_
    intro H
    have ha := nativeL2ParticularCLM_agrees_continuous hκ0 hκ1 V hminus hplus H
    change HasWeakPartialDeriv k _ _ _
    rw [ha.2.1 j,ha.2.2 k j]
    exact (nativeL2ParticularCollar_H2_and_jets hκ0 hκ1 V hminus hplus H.val H.property).2.2 k j

theorem nativeL2ParticularCLM_memH2
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F) nativePoissonEntranceCollar := by
  have h := nativeL2ParticularCLM_weak_jets hκ0 hκ1 V hminus hplus F
  apply memWkp_succ_of_weakDerivatives (nativePolarTimeWindow_open (1/2)) (by norm_num : (1:ℝ≥0∞)≤2)
    (Lp.memLp _) (g := fun j => nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus j F)
  · intro j
    apply MemWkp.one_iff_memW1p.mpr
    exact ⟨Lp.memLp _,fun k => ⟨_,Lp.memLp _,h.2 k j⟩⟩
  · exact h.1

#print axioms nativeL2ParticularLinear_bounds
#print axioms nativeL2ParticularCLM_agrees_continuous
#print axioms nativeL2ParticularCLM_weak_jets
#print axioms nativeL2ParticularCLM_memH2
end Yamabe3.Analysis.SpherePolar
