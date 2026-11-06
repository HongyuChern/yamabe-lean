import Yamabe3.Analysis.NativeHalfEndH4Regularity
import Yamabe3.Analysis.WeakFlatEquationH4Estimate
import Yamabe3.Analysis.NativeH4CollarRealization

/-! Genuine local gain and quantitative H4 estimates for a homogeneous
collar jet. These are auxiliary consumers of the same jet equation; the
outer-field producer supplies that equation separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

lemma weakNegativeLaplacian_restrict_collar {V:Set E} (hV:IsOpen V)
    (hVD:V⊆nativePoissonEntranceCollar) (J:nativeCollarJetClosure) :
    weakNegativeLaplacian nativePoissonEntranceCollar J.val.1=ᵐ[volume.restrict V]
      weakNegativeLaplacian V J.val.1 := by
  filter_upwards [eventually_all.mpr (fun i:Fin 3=>
    iterWeakPartial_mono_set_ae (by norm_num:(1:ℝ≥0∞)≤2) hV hVD
      (fun _:Fin 2=>i) (nativeCollarJetClosure_memH2 J))] with x hx
  simp only [weakNegativeLaplacian,hx]

theorem nativeHomogeneousCollar_local_H4 (q:E→ℝ)
    (hq:ContDiffOn ℝ ∞ q ({0}ᶜ:Set E)) (J:nativeCollarJetClosure)
    (heq:weakNegativeLaplacian nativePoissonEntranceCollar J.val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x=>q x*J.val.1 x)) :
    MemWkpLocally 4 (J.val.1:E→ℝ) nativePoissonEntranceCollar := by
  have hD:=nativePolarTimeWindow_open (1/2)
  have hu:=nativeCollarJetClosure_memH2 J
  let p:=fun i:Fin 3=>chosenWeakPartial' 2 i J.val.1 nativePoissonEntranceCollar
  have he:WeakEquation nativePoissonEntranceCollar (matrixFlux (fun _:E=>(1:Matrix (Fin 3) (Fin 3) ℝ)) p)
      (fun x=>0+q x*J.val.1 x):=by
    intro φ hφ hc hs
    have h:=weakNegativeLaplacian_test_identity hD hu φ hφ hc hs
    have hh:=integral_congr_ae (heq.mul (EventuallyEq.refl _ φ))
    have hf:matrixFlux (fun _:E=>(1:Matrix (Fin 3) (Fin 3) ℝ)) p=p:=by
      funext i x
      simp [matrixFlux,Matrix.one_apply]
    rw [hf]
    simpa only [p,Pi.mul_apply,zero_add,nativePoissonEntranceCollar] using h.trans hh
  exact memWkpLocally_four_of_local_potential_H2_source
    (A:=fun _:E=>(1:Matrix (Fin 3) (Fin 3) ℝ))
    isClosed_singleton.isOpen_compl hD (nativePolarTimeWindow_precompact (1/2))
    (nativePolarTimeWindow_closure_offZero (1/2))
    (fun _ _=>contDiff_const) (fun _ _=>Matrix.PosDef.one) hq
    (MemWkpLocally.zero hD 2) hu.memLp
    (fun i=>chosenWeakPartial'_memLp_of_mem hu.memW1p i)
    (fun i=>chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i) he

theorem exists_nativeHomogeneousCollar_H4_bound {V W:Set E}
    (hV:IsOpen V) (hVc:IsCompact (closure V)) (hVD:closure V⊆nativePoissonEntranceCollar)
    (hW:IsOpen W) (hWc:IsCompact (closure W)) (hWV:closure W⊆V)
    {Q:ℝ} (hQ:0≤Q) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀q:E→ℝ,ContDiffOn ℝ ∞ q ({0}ᶜ:Set E)→
      (∀n≤2,∀x∈V,‖iteratedFDeriv ℝ n q x‖≤Q)→
      ∀J:nativeCollarJetClosure,
      weakNegativeLaplacian nativePoissonEntranceCollar J.val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x=>q x*J.val.1 x)→
      MemWkp 4 2 (J.val.1:E→ℝ) W ∧
      iteratedWeakSobolevNorm 4 2 J.val.1 W≤C*ENNReal.ofReal ‖J.val.1‖ := by
  obtain ⟨C,hC,hb⟩:=exists_uniform_weak_flat_equation_H4_estimate hV hVc hW hWc hWV hQ
  refine ⟨C,hC,fun q hq hqj J heq=>?_⟩
  have hu4:=nativeHomogeneousCollar_local_H4 q hq J heq
  have hVD':V⊆nativePoissonEntranceCollar:=subset_closure.trans hVD
  have huV:=(nativeCollarJetClosure_memH2 J).mono_set (by norm_num:(1:ℝ≥0∞)≤2) hV hVD'
  have hl:weakNegativeLaplacian V J.val.1=ᵐ[volume.restrict V] (fun x=>q x*J.val.1 x):=
    (weakNegativeLaplacian_restrict_collar hV hVD' J).symm.trans
      (ae_mono (Measure.restrict_mono hVD' le_rfl) heq)
  have he:∀φ:E→ℝ,ContDiff ℝ ∞ φ→HasCompactSupport φ→tsupport φ⊆V→
      (∫x in V,∑i:Fin 3,chosenWeakPartial' 2 i J.val.1 V x*partialDeriv i φ x)=
        ∫x in V,((fun _:E=>0) x+q x*J.val.1 x)*φ x:=by
    intro φ hφ hc hs
    rw [weakNegativeLaplacian_test_identity hV huV φ hφ hc hs]
    simpa only [zero_add,Pi.mul_apply] using integral_congr_ae (hl.mul (EventuallyEq.refl _ φ))
  have hqD:=hq.mono (subset_closure.trans (nativePolarTimeWindow_closure_offZero (1/2)))
  have hh:=hb nativePoissonEntranceCollar (nativePolarTimeWindow_open (1/2)) hVD q hqD hqj
    J.val.1 (fun _:E=>0) hu4 (MemWkp_zero_fun (by norm_num) hV) he
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [wkpNorm_zero_fun_zero (by norm_num) hV,add_zero,wkpNorm_zero]
  have hn:eLpNorm (J.val.1:E→ℝ) 2 (volume.restrict nativePoissonEntranceCollar)=ENNReal.ofReal ‖J.val.1‖:=by
    rw [←Lp.enorm_def,←ofReal_norm]
  rw [←hn]
  exact mul_le_mul le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono hVD' le_rfl)) zero_le zero_le

#print axioms weakNegativeLaplacian_restrict_collar
#print axioms nativeHomogeneousCollar_local_H4
#print axioms exists_nativeHomogeneousCollar_H4_bound
end Yamabe3.Analysis.SpherePolar
