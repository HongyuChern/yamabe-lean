import Yamabe3.Analysis.DirectionalH2Estimate
import Yamabe3.Analysis.BoundaryThirdDerivativeRecovery

/-! A source-uniform H3 estimate on one open piece uses actual global
tangential source derivatives; no normal matching of the source is imposed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_directional_piece_H3_estimate
    (B : SmoothEllipticBilinearForm 3 univ)
    {O V W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V⊆O)
    (hW : IsOpen W) (hWV : W⊆V) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ u f : E → ℝ, ∀ r : Fin 3 → E → ℝ,
      MemWkp 2 2 u O → MemLp f 2 (volume.restrict O) → MemWkp 1 2 f W →
      (∀ k : Fin 3,k≠0 → MemLp (r k) 2 (volume.restrict O)) →
      (∀ k : Fin 3,k≠0 → HasWeakPartialDeriv k (r k) f O) →
      (∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
        (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
          fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,f x*φ x) →
      MemWkp 3 2 u W ∧ iteratedWeakSobolevNorm 3 2 u W ≤ C *
        (iteratedWeakSobolevNorm 2 2 u O+iteratedWeakSobolevNorm 1 2 f W+
          ∑ k ∈ (Finset.univ : Finset (Fin 3)).erase 0,iteratedWeakSobolevNorm 0 2 (r k) O) := by
  classical
  choose D hD hd using fun k : Fin 3 => exists_directional_H2_estimate B hO hOc hV hVc hVO k
  have hWc : IsCompact (closure W) := hVc.of_isClosed_subset isClosed_closure (closure_mono hWV)
  have hWO : W⊆O := hWV.trans (subset_closure.trans hVO)
  obtain ⟨K,hK,hb⟩ := exists_normal_H3_recovery_bound B hW hWc
  let S : ℝ≥0∞ := ∑ k : Fin 3,D k
  have hS : S≠⊤ := ENNReal.sum_ne_top.mpr (fun k _ => hD k)
  refine ⟨K*(1+S),by finiteness,?_⟩
  intro u f r hu hf hfW hr hfr heq
  let R : ℝ≥0∞ := ∑ k ∈ (Finset.univ : Finset (Fin 3)).erase 0,iteratedWeakSobolevNorm 0 2 (r k) O
  let N := iteratedWeakSobolevNorm 2 2 u O+iteratedWeakSobolevNorm 1 2 f W+R
  have hu3 := directional_source_H3_on_piece B hO hOc hV hVc hVO hW hWV hu hf hfW.memW1p
    (fun k hk => ⟨hf,r k,hr k hk,hfr k hk⟩) heq
  have hp (k : Fin 3) (hk : k≠0) :
      iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 k u W) W ≤ D k*N := by
    have hpk := hd k u f (r k) hu hf (hr k hk) (hfr k hk) heq
    have hrk : iteratedWeakSobolevNorm 0 2 (r k) O ≤ R :=
      Finset.single_le_sum (f:=fun k : Fin 3 => iteratedWeakSobolevNorm 0 2 (r k) O) (fun _ _ => zero_le) (Finset.mem_erase.mpr ⟨hk,Finset.mem_univ k⟩)
    rw [← wkpNorm_congr_ae (k:=2) (by norm_num : (1:ℝ≥0∞)≤2) hW
      (chosenWeakPartial'_mono_set_ae (by norm_num) hW hWO hu.memW1p k)]
    calc
      _ ≤ iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 k u O) V :=
        wkpNorm_mono_set (by norm_num) hW hWV hpk.1
      _ ≤ D k*(iteratedWeakSobolevNorm 2 2 u O+iteratedWeakSobolevNorm 0 2 (r k) O) := hpk.2
      _ ≤ D k*N := mul_le_mul le_rfl
        (add_le_add (le_add_right le_rfl) hrk) zero_le zero_le
  have hs : (∑ k ∈ (Finset.univ : Finset (Fin 3)).erase 0,
      iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 k u W) W) ≤ S*N := by
    calc
      _ ≤ ∑ k ∈ (Finset.univ : Finset (Fin 3)).erase 0,D k*N :=
        Finset.sum_le_sum (fun k hk => hp k (Finset.mem_erase.mp hk).1)
      _ ≤ ∑ k : Fin 3,D k*N :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => zero_le)
      _ = _ := by simp only [S,Finset.sum_mul]
  refine ⟨hu3,?_⟩
  calc
    _ ≤ K*(iteratedWeakSobolevNorm 2 2 u W+iteratedWeakSobolevNorm 1 2 f W+
        ∑ k ∈ (Finset.univ : Finset (Fin 3)).erase 0,iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 k u W) W) :=
      hb u f hu3 hfW (localized_principal_restrict_canonical hW hWO hu.memW1p heq)
    _ ≤ K*(N+S*N) := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      apply add_le_add _ hs
      exact (add_le_add (wkpNorm_mono_set (by norm_num) hW hWO hu) le_rfl).trans (le_add_right le_rfl)
    _ = _ := by ring

#print axioms exists_directional_piece_H3_estimate
end Yamabe3.Analysis.UniformElliptic
