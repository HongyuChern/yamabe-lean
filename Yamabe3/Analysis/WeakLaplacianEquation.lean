import Yamabe3.Analysis.WeakLaplacianSobolev
import Yamabe3.Analysis.UniformElliptic.UniformH2Profile

/-! The actual weak negative Laplacian is the source of the retained weak
Euclidean equation. Equality is proved in volume measure, not on a boundary. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weakNegativeLaplacian_test_identity {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (hu : MemWkp 2 2 u O)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    (∫ x in O, ∑ i : Fin d, chosenWeakPartial' 2 i u O x * partialDeriv i φ x) =
      ∫ x in O, weakNegativeLaplacian O u x * φ x := by
  classical
  let p (i : Fin d) := chosenWeakPartial' 2 i u O
  let g (i : Fin d) := chosenWeakPartial' 2 i (p i) O
  have hp (i : Fin d) : MemWkp 1 2 (p i) O := hu.chosenWeakPartial_mem i
  have hg (i : Fin d) : MemLp (g i) 2 (volume.restrict O) :=
    chosenWeakPartial'_memLp_of_mem (hp i).memW1p i
  have hpi (i : Fin d) : Integrable (fun x => p i x*partialDeriv i φ x) (volume.restrict O) := by
    exact integrable_mul_test ((hp i).memLp.locallyIntegrable (by norm_num))
      (contDiff_partial hφ i) (hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
  have hgi (i : Fin d) : Integrable (fun x => g i x*φ x) (volume.restrict O) :=
    integrable_mul_test ((hg i).locallyIntegrable (by norm_num)) hφ hc
  have hid (i : Fin d) : (∫ x in O, p i x*partialDeriv i φ x) = -(∫ x in O, g i x*φ x) :=
    chosenWeakPartial'_isWeakPartial_of_mem (hp i).memW1p i φ hφ hc hs
  calc
    _ = ∑ i : Fin d, ∫ x in O, p i x*partialDeriv i φ x :=
      integral_finset_sum _ (fun i _ => hpi i)
    _ = ∑ i : Fin d, -(∫ x in O, g i x*φ x) := Finset.sum_congr rfl (fun i _ => hid i)
    _ = -(∫ x in O, ∑ i : Fin d, g i x*φ x) := by
      rw [integral_finset_sum _ (fun i _ => hgi i), Finset.sum_neg_distrib]
    _ = ∫ x in O, -(∑ i : Fin d, g i x)*φ x := by
      rw [← integral_neg]
      congr 1
      funext x
      rw [neg_mul, Finset.sum_mul]
    _ = _ := rfl

theorem weakNegativeLaplacian_eq_source_ae {O : Set E} (hO : IsOpen O)
    {u f : E → ℝ} (hu : MemWkp 2 2 u O)
    (hf : LocallyIntegrable f (volume.restrict O))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i : Fin d, chosenWeakPartial' 2 i u O x*partialDeriv i φ x) = ∫ x in O, f x*φ x) :
    weakNegativeLaplacian O u =ᵐ[volume.restrict O] f := by
  have hl := ((weakNegativeLaplacian_mem_bound hO 0 hu).1.memLp).locallyIntegrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  suffices hh : (fun x => weakNegativeLaplacian O u x-f x) =ᵐ[volume.restrict O] 0 by
    filter_upwards [hh] with x hx
    exact sub_eq_zero.mp hx
  change ∀ᵐ x ∂volume.restrict O, weakNegativeLaplacian O u x-f x = 0
  rw [ae_restrict_iff' hO.measurableSet]
  apply hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hl.sub hf))
  intro φ hφ hc hs
  have hid := (weakNegativeLaplacian_test_identity hO hu φ hφ hc hs).symm.trans (heq φ hφ hc hs)
  have hzero : ∀ x, x ∉ O → φ x • (fun x => weakNegativeLaplacian O u x-f x) x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]
  change (∫ x : E, φ x • (fun x => weakNegativeLaplacian O u x-f x) x) = 0
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  simp only [smul_eq_mul, mul_sub]
  simp_rw [mul_comm (φ _)]
  rw [integral_sub (integrable_mul_test hl hφ hc) (integrable_mul_test hf hφ hc), hid, sub_self]

#print axioms weakNegativeLaplacian_test_identity
#print axioms weakNegativeLaplacian_eq_source_ae
end Yamabe3.Analysis.UniformElliptic
