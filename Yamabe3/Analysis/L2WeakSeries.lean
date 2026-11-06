/-
Copyright (c) 2026 The PoincareLib contributors.
Copyright 2026 The DifferentialGeometry contributors
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/WeakDerivativeLimit.lean
Earlier source credited by PoincareLib at DifferentialGeometry 1b535dd102b94cc42b107cca27059687888f08b3.
  DifferentialGeometry/Analysis/Sobolev/Tools/WeakPartialLimit.lean

Uses the compact-test L2 estimates in weak differentiation of finite sums and L2 series.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.L2FiniteSquareSummability
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Iterated.WeakDerivatives
import Yamabe3.Analysis.UniformElliptic.NativeC1StrongLimit
import Yamabe3.Analysis.UniformElliptic.WeakSobolevCauchyLimit

/-! Actual weak differentiation is closed under strongly convergent L2
series. The same value sum and its first and second sums are bound together. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem native_weakPartial_transfer_ae {Ω : Set E} {f g f' g' : E → ℝ}
    {i : Fin d} (hf : f' =ᵐ[volume.restrict Ω] f)
    (hg : g' =ᵐ[volume.restrict Ω] g) (hw : HasWeakPartialDeriv i g f Ω) :
    HasWeakPartialDeriv i g' f' Ω := by
  intro φ hφ hc hs
  calc
    _ = ∫ x in Ω,f x*fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      integral_congr_ae (hf.mul ae_eq_rfl)
    _ = -(∫ x in Ω,g x*φ x) := hw φ hφ hc hs
    _ = _ := congrArg Neg.neg (integral_congr_ae (hg.mul ae_eq_rfl)).symm

theorem native_weakPartial_Lp_finset_sum {ι : Type*} {Ω : Set E}
    {u v : ι → Lp ℝ 2 (volume.restrict Ω)} {i : Fin d}
    (hw : ∀ a,HasWeakPartialDeriv i (v a) (u a) Ω) (s : Finset ι) :
    HasWeakPartialDeriv i (⇑(∑ a ∈ s,v a)) (⇑(∑ a ∈ s,u a)) Ω := by
  apply native_weakPartial_transfer_ae (lp_finset_sum_coe_ae u s) (lp_finset_sum_coe_ae v s)
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 (volume.restrict Ω) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict Ω
  have hdφLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict Ω
  simp_rw [Finset.sum_mul]
  have hl (a : ι) : Integrable (fun x => u a x*fderiv ℝ φ x (EuclideanSpace.single i 1))
      (volume.restrict Ω) := (Lp.memLp (u a)).integrable_mul hdφLp
  have hr (a : ι) : Integrable (fun x => v a x*φ x) (volume.restrict Ω) :=
    (Lp.memLp (v a)).integrable_mul hφLp
  rw [integral_finsetSum s (fun a _ => hl a),integral_finsetSum s (fun a _ => hr a)]
  simp_rw [hw _ φ hφ hc hs]
  simp only [Finset.sum_neg_distrib]

theorem native_weakPartial_Lp_tsum {ι : Type*} {Ω : Set E}
    {u v : ι → Lp ℝ 2 (volume.restrict Ω)} {i : Fin d}
    (hu : Summable u) (hv : Summable v)
    (hw : ∀ a,HasWeakPartialDeriv i (v a) (u a) Ω) :
    HasWeakPartialDeriv i (⇑(∑' a,v a)) (⇑(∑' a,u a)) Ω := by
  exact native_weak_partial_of_tendsto_L2_filter i hu.hasSum hv.hasSum
    (native_weakPartial_Lp_finset_sum hw)

theorem native_memWkp_two_Lp_series {ι : Type*} {Ω : Set E} (hΩ : IsOpen Ω)
    (u : ι → Lp ℝ 2 (volume.restrict Ω))
    (p : Fin d → ι → Lp ℝ 2 (volume.restrict Ω))
    (q : Fin d → Fin d → ι → Lp ℝ 2 (volume.restrict Ω))
    (hu : Summable u) (hp : ∀ i,Summable (p i)) (hq : ∀ k i,Summable (q k i))
    (hup : ∀ a i,HasWeakPartialDeriv i (p i a) (u a) Ω)
    (hpq : ∀ a k i,HasWeakPartialDeriv k (q k i a) (p i a) Ω) :
    MemWkp 2 2 (⇑(∑' a,u a)) Ω ∧
      (∀ i,HasWeakPartialDeriv i (⇑(∑' a,p i a)) (⇑(∑' a,u a)) Ω) ∧
      (∀ k i,HasWeakPartialDeriv k (⇑(∑' a,q k i a)) (⇑(∑' a,p i a)) Ω) := by
  have h1 (i : Fin d) := native_weakPartial_Lp_tsum hu (hp i) (fun a => hup a i)
  have h2 (k i : Fin d) := native_weakPartial_Lp_tsum (hp i) (hq k i) (fun a => hpq a k i)
  refine ⟨?_,h1,h2⟩
  apply memWkp_succ_of_weakDerivatives hΩ (by norm_num : (1:ℝ≥0∞)≤2)
    (Lp.memLp _) (g := fun i => ⇑(∑' a,p i a))
  · intro i
    apply MemWkp.one_iff_memW1p.mpr
    exact ⟨Lp.memLp _,fun k => ⟨_,Lp.memLp _,h2 k i⟩⟩
  · exact h1

#print axioms native_weakPartial_Lp_tsum
#print axioms native_memWkp_two_Lp_series
end Yamabe3.Analysis.UniformElliptic
