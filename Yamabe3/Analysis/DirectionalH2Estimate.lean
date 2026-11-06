import Yamabe3.Analysis.WeakDivergenceH2Estimate
import Yamabe3.Analysis.DirectionalCommutatorBound

/-! A quantitative estimate for one chosen derivative of the same weak
solution uses only the actual L2 derivative of the source in that direction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_locally_H2_weak_source_estimate
    (B : SmoothEllipticBilinearForm 3 univ)
    {V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W⊆V) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ {O : Set E}, closure V⊆O →
      ∀ u f : E → ℝ, MemW1p 2 u O → MemWkpLocally 2 u O → MemLp f 2 (volume.restrict O) →
      (∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
        (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
          fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,f x*φ x) →
      iteratedWeakSobolevNorm 2 2 u W ≤ C *
        (iteratedWeakSobolevNorm 0 2 u V+iteratedWeakSobolevNorm 0 2 f V) := by
  obtain ⟨C,hC,hb⟩ := exists_weak_divergence_H2_operator_estimate B hV hVc hW hWc hWV
  refine ⟨C,hC,?_⟩
  intro O hVO u f hu hu2 hf heq
  have hs : V⊆O := subset_closure.trans hVO
  have he := weakDivergenceSource_eq_source_ae hV hVc B.a B.smooth_a
    (memWkp_on_precompact_of_locally hu2 hV hVc hVO) (hf.mono_measure (Measure.restrict_mono hs le_rfl))
    (localized_principal_restrict_canonical hV hs hu heq)
  simpa only [wkpNorm_congr_ae (k:=0) (by norm_num : (1:ℝ≥0∞)≤2) hV he] using hb u hVO hu2

theorem exists_directional_H2_estimate
    (B : SmoothEllipticBilinearForm 3 univ)
    {O W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWO : closure W⊆O) (k : Fin 3) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ u f r : E → ℝ,
      MemWkp 2 2 u O → MemLp f 2 (volume.restrict O) → MemLp r 2 (volume.restrict O) →
      HasWeakPartialDeriv k r f O →
      (∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
        (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
          fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,f x*φ x) →
      MemWkp 2 2 (chosenWeakPartial' 2 k u O) W ∧
      iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 k u O) W ≤ C *
        (iteratedWeakSobolevNorm 2 2 u O+iteratedWeakSobolevNorm 0 2 r O) := by
  obtain ⟨V,hV,hWV,hVO⟩ := hWc.exists_isOpen_closure_subset (hO.mem_nhdsSet.mpr hWO)
  have hVc : IsCompact (closure V) := hOc.of_isClosed_subset isClosed_closure (hVO.trans subset_closure)
  obtain ⟨C,hC,hb⟩ := exists_locally_H2_weak_source_estimate B hV hVc hW hWc hWV
  obtain ⟨D,hD,hd⟩ := exists_explicit_directional_source_bound hO hOc B.a B.smooth_a k
  refine ⟨C*(1+D), by finiteness, ?_⟩
  intro u f r hu hf hr hfr heq
  let p := chosenWeakPartial' 2 k u O
  let G := differentiatedSource B.a (fun j => chosenWeakPartial' 2 j u O)
    (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) r k
  have hGe := explicit_directional_source_equation hO hOc B.a B.smooth_a hu hf hr k hfr heq
  have hpLoc := directional_weak_source_local_H2 hO hOc B.a B.smooth_a
    (fun x _ => smoothElliptic_matrix_posDef B x) hu hf hr k hfr heq
  have hpm : MemWkp 1 2 p O := hu.chosenWeakPartial_mem k
  have hpV : iteratedWeakSobolevNorm 0 2 p V ≤ iteratedWeakSobolevNorm 2 2 u O :=
    (wkpNorm_mono_set (by norm_num) hV (subset_closure.trans hVO) hpm.le_succ).trans
      ((wkpNorm_mono_order (by norm_num : 0≤1) p O).trans
        (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 u O k))
  have hGV : iteratedWeakSobolevNorm 0 2 G V ≤ iteratedWeakSobolevNorm 0 2 r O+
      D*iteratedWeakSobolevNorm 2 2 u O :=
    (wkpNorm_mono_set (k:=0) (by norm_num) hV (subset_closure.trans hVO) hGe.1).trans (hd u r hu hr)
  refine ⟨memWkp_on_precompact_of_locally hpLoc hW hWc hWO, ?_⟩
  calc
    _ ≤ C*(iteratedWeakSobolevNorm 0 2 p V+iteratedWeakSobolevNorm 0 2 G V) :=
      hb hVO p G hpm.memW1p hpLoc hGe.1 hGe.2
    _ ≤ C*(iteratedWeakSobolevNorm 2 2 u O+(iteratedWeakSobolevNorm 0 2 r O+D*iteratedWeakSobolevNorm 2 2 u O)) :=
      mul_le_mul le_rfl (add_le_add hpV hGV) zero_le zero_le
    _ ≤ C*(1+D)*(iteratedWeakSobolevNorm 2 2 u O+iteratedWeakSobolevNorm 0 2 r O) := by
      calc
        _ ≤ C*(iteratedWeakSobolevNorm 2 2 u O+(iteratedWeakSobolevNorm 0 2 r O+
            D*(iteratedWeakSobolevNorm 2 2 u O+iteratedWeakSobolevNorm 0 2 r O))) := by gcongr; exact le_add_right le_rfl
        _ = _ := by ring

#print axioms exists_locally_H2_weak_source_estimate
#print axioms exists_directional_H2_estimate
end Yamabe3.Analysis.UniformElliptic
