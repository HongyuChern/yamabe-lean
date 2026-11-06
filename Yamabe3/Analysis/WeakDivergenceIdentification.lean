import Yamabe3.Analysis.WeakDivergenceOperatorContinuity

/-! Identify the actual weak operator with its given source and with the
classical principal source on smooth inputs, retaining the same function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weakDivergenceSource_congr_ae {O : Set E} (hO : IsOpen O)
    (a : E → Matrix (Fin d) (Fin d) ℝ) {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict O] v) :
    weakDivergenceSource O a u =ᵐ[volume.restrict O] weakDivergenceSource O a v := by
  have hp (j : Fin d) := chosenWeakPartial'_ae_congr (by norm_num : (1:ℝ≥0∞)≤2) hO huv j
  have hq (i j : Fin d) := chosenWeakPartial'_ae_congr (by norm_num : (1:ℝ≥0∞)≤2) hO (hp j) i
  filter_upwards [eventually_all.mpr hp, eventually_all.mpr (fun i => eventually_all.mpr (hq i))] with x hx hy
  simp only [weakDivergenceSource, hx, hy]

theorem weakDivergenceSource_eq_source_ae {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u f : E → ℝ} (hu : MemWkp 2 2 u O) (hf : MemLp f 2 (volume.restrict O))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
      (∫ x in O, ∑ i, ∑ j, a x i j*chosenWeakPartial' 2 j u O x*
        fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O, f x*φ x) :
    weakDivergenceSource O a u =ᵐ[volume.restrict O] f := by
  filter_upwards [weak_hessian_equation_ae hO hOc a ha hu hf heq] with x hx
  change -(∑ i,∑ j,(a x i j*chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O x+
    fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1)*chosenWeakPartial' 2 j u O x))=f x
  rw [hx, neg_neg]

theorem contDiff_principalSource (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (principalSource a u) := by
  apply ContDiff.neg
  apply ContDiff.sum
  intro i _
  apply contDiff_partial
  exact ContDiff.sum (fun j _ => (ha i j).mul (contDiff_partial hu j))

theorem weakDivergenceSource_smooth_ae {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) (hum : MemWkp 2 2 u O) :
    weakDivergenceSource O a u =ᵐ[volume.restrict O] principalSource a u := by
  apply weakDivergenceSource_eq_source_ae hO hOc a ha hum
    ((continuous_memLp_on_compact (contDiff_principalSource a ha hu).continuous hOc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl))
  intro φ hφ hc hs
  calc
    _ = ∫ x in O,∑ i, matrixFlux a (fun j => partialDeriv j u) i x*partialDeriv i φ x := by
      apply integral_congr_ae
      filter_upwards [eventually_all.mpr (fun j => chosenWeakPartial_smooth_ae_eq (by norm_num) hO hu hum.memW1p j)] with x hx
      simp only [matrixFlux, Finset.sum_mul, partialDeriv, hx]
    _ = _ := weakEquation_principalSource hO ha hu φ hφ hc hs

#print axioms weakDivergenceSource_congr_ae
#print axioms weakDivergenceSource_eq_source_ae
#print axioms weakDivergenceSource_smooth_ae
end Yamabe3.Analysis.UniformElliptic
