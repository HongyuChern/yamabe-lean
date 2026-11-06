/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/NormalDerivative.lean

Uses the compact-test integrability calculation in the almost-everywhere strong
divergence equation.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryLocalH4
import PoincareLib.Analysis.Elliptic.Regularity.Iteration.TestCalculus

/-! Actual almost-everywhere divergence identity from the weak equation.
This retains the sign and the same source, and is intended for quantitative
normal recovery. It is not a new existence theorem or a boundary trace. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The original divergence weak equation determines the sum of the actual
flux derivatives, with the minus sign preserved. -/
theorem divergence_eq_neg_source_ae
    {O : Set E} (hO : IsOpen O) {F D : Fin d → E → ℝ} {f : E → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict O))
    (hD : ∀ i, MemLp (D i) 2 (volume.restrict O))
    (hf : MemLp f 2 (volume.restrict O))
    (hw : ∀ i, HasWeakPartialDeriv i (D i) (F i) O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in O, f x * φ x) :
    (fun x => ∑ i, D i x) =ᵐ[volume.restrict O] (fun x => -f x) := by
  let G : E → ℝ := fun x => (∑ i, D i x) + f x
  have hG : MemLp G 2 (volume.restrict O) :=
    (memLp_finsetSum _ (fun i _ => hD i)).add hf
  have hz : G =ᵐ[volume.restrict O] 0 := by
    change ∀ᵐ x ∂volume.restrict O, G x = 0
    rw [ae_restrict_iff' hO.measurableSet]
    apply hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (locallyIntegrableOn_of_locallyIntegrable_restrict (hG.locallyIntegrable (by norm_num)))
    intro φ hφ hc hs
    have hφLp : MemLp φ 2 (volume.restrict O) :=
      (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
    have hDLp (i : Fin d) : MemLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 (volume.restrict O) :=
      (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ _)).restrict O
    have hdint (i : Fin d) : Integrable (fun x => D i x * φ x) (volume.restrict O) :=
      (hD i).integrable_mul hφLp
    have hfint : Integrable (fun x => f x * φ x) (volume.restrict O) :=
      hf.integrable_mul hφLp
    have he := heq φ hφ hc hs
    have hsum := integral_finsetSum Finset.univ (fun i _ => (hF i).integrable_mul (hDLp i))
    simp only [Pi.mul_apply] at hsum
    rw [hsum] at he
    simp_rw [hw _ φ hφ hc hs] at he
    rw [Finset.sum_neg_distrib] at he
    have hzero : ∀ x, x ∉ O → φ x • G x = 0 := by
      intro x hx
      simp [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    simp only [smul_eq_mul, G, mul_add, Finset.mul_sum]
    simp_rw [mul_comm (φ _)]
    rw [integral_add (integrable_finsetSum _ (fun i _ => hdint i)) hfint,
      integral_finsetSum _ (fun i _ => hdint i)]
    linarith
  filter_upwards [hz] with x hx
  change (∑ i, D i x) + f x = 0 at hx
  linarith

#print axioms divergence_eq_neg_source_ae
end Yamabe3.Analysis.UniformElliptic
