import Yamabe3.Analysis.FiniteRegularityExtension
import Yamabe3.Analysis.WeakGeometricPerturbation

/-! Weak first and second coordinate derivatives agree with the genuine
classical derivatives on precompact subsets of a C2 domain. This finite
regularity statement applies to the actual H4 Banach graph representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem chosenWeakPartial_classical_on_precompact
    {O W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hW : IsOpen W) (hOW : closure O ⊆ W) {u : E → ℝ}
    (hu : ContDiffOn ℝ 1 u W) (hu1 : MemWkp 1 2 u O) (i : Fin 3) :
    chosenWeakPartial' 2 i u O =ᵐ[volume.restrict O] partialDeriv i u := by
  obtain ⟨v,hv,hvc,hvu⟩ := exists_finite_compact_extension_near_compact 1 hW hOc hOW hu
  have he : v =ᵐ[volume.restrict O] u := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact (hvu x (subset_closure hx)).self_of_nhds
  have hv1 := (MemWkp_congr_ae (by norm_num : (1:ℝ≥0∞) ≤ 2) hO he).mpr hu1
  have hd : MemLp (partialDeriv i v) 2 (volume.restrict O) :=
    ((((hv.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hvc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)))).restrict O
  have hw := HasWeakPartialDeriv.ae_eq hO (chosenWeakPartial'_isWeakPartial_of_mem hv1.memW1p i)
    (HasWeakPartialDeriv.of_contDiff hO hv)
    ((chosenWeakPartial'_memLp_of_mem hv1.memW1p i).locallyIntegrable (by norm_num))
    (hd.locallyIntegrable (by norm_num))
  have hj := chosenWeakPartial'_ae_congr (by norm_num : (1:ℝ≥0∞) ≤ 2) hO he i
  filter_upwards [hj,hw,ae_restrict_mem hO.measurableSet] with x hx hd hxO
  rw [← hx,hd]
  exact congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
    ((hvu x (subset_closure hxO)).fderiv_eq)

theorem chosenWeakSecond_classical_on_precompact
    {O W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hW : IsOpen W) (hOW : closure O ⊆ W) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u W) (hu2 : MemWkp 2 2 u O) (i j : Fin 3) :
    chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O =ᵐ[volume.restrict O]
      partialDeriv i (partialDeriv j u) := by
  have hj := chosenWeakPartial_classical_on_precompact hO hOc hW hOW
    (hu.of_le (by norm_num)) hu2.le_succ j
  have hp : ContDiffOn ℝ 1 (partialDeriv j u) W :=
    (hu.fderiv_of_isOpen hW (by norm_num)).clm_apply contDiffOn_const
  have hp1 := (MemWkp_congr_ae (by norm_num : (1:ℝ≥0∞) ≤ 2) hO hj).mp (hu2.chosenWeakPartial_mem j)
  exact (chosenWeakPartial'_ae_congr (by norm_num) hO hj i).trans
    (chosenWeakPartial_classical_on_precompact hO hOc hW hOW hp hp1 i)

theorem weakSecondOrderPerturbation_classical_ae
    {O W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hW : IsOpen W) (hOW : closure O ⊆ W) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u W) (hu2 : MemWkp 2 2 u O)
    (a : Fin 3 → Fin 3 → E → ℝ) (b : Fin 3 → E → ℝ) (c : E → ℝ) :
    weakSecondOrderPerturbation O a b c u =ᵐ[volume.restrict O] secondOrderPerturbation a b c u := by
  filter_upwards [eventually_all.mpr (fun i : Fin 3 => eventually_all.mpr (fun j : Fin 3 =>
    chosenWeakSecond_classical_on_precompact hO hOc hW hOW hu hu2 i j)),
    eventually_all.mpr (fun j : Fin 3 => chosenWeakPartial_classical_on_precompact hO hOc hW hOW
      (hu.of_le (by norm_num)) hu2.le_succ j)] with x h2 h1
  simp only [weakSecondOrderPerturbation,secondOrderPerturbation,h2,h1]

#print axioms chosenWeakPartial_classical_on_precompact
#print axioms chosenWeakSecond_classical_on_precompact
#print axioms weakSecondOrderPerturbation_classical_ae
end Yamabe3.Analysis.UniformElliptic
