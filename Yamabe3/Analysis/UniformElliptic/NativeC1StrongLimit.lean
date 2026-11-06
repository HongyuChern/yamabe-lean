/-
Copyright (c) 2026 The PoincareLib contributors.
Copyright 2026 The DifferentialGeometry contributors
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/WeakDerivativeLimit.lean
Earlier source credited by PoincareLib at DifferentialGeometry 1b535dd102b94cc42b107cca27059687888f08b3.
  DifferentialGeometry/Analysis/Sobolev/Tools/WeakPartialLimit.lean

Carries the compact-test integration-by-parts proof through the local C1 approximation
work, renames the helper and uses it in the strong H1 limit.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.UniformElliptic.NativeL2SquareConvergence
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Weak.Witnesses
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Strong weak-gradient limits of the same locally C1 physical field

The input consists of actual square integrals of the original functions
and their classical derivatives. Completeness constructs the derivative
limits, and integration by parts identifies them with weak derivatives
of the specified value limit. The index may be any directed semilattice,
including finite spectral sets; no enumeration or subsequence is chosen.

The C1 integration-by-parts proof below is reused from the accepted
`C1ApproximationH1.integral_mul_partial_test_of_contDiffOn_one`, with
only its name changed. It is isolated here to avoid importing the
unneeded high-order uniform elliptic estimate chain. The original module
and every original proof remain unchanged.

This is a strong H1 closure theorem. It does not assert the two-index
gradient estimate for the forced half-end, and it imposes no zero trace.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis.UniformElliptic

variable {ι X : Type*} [MeasurableSpace X]

/-- The same real square integrals characterize L2 convergence for an
arbitrary filter, not only an enumerated sequence. -/
theorem native_tendsto_toLp_of_integral_sq_sub_filter
    {l : Filter ι} {μ : Measure X} {f : ι → X → ℝ} {u : X → ℝ}
    (hf : ∀ a, MemLp (f a) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun a => ∫ x, (f a x - u x) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun a => (hf a).toLp (f a)) l (𝓝 (hu.toLp u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 (ε ^ 2) (sq_pos_of_pos hε)] with a ha
  rw [dist_eq_norm]
  have hsquare := native_norm_toLp_sub_sq_eq_integral_sq (hf a) hu
  nlinarith [norm_nonneg ((hf a).toLp (f a) - hu.toLp u)]

/-- A two-index bound on the original square differences constructs a
genuine L2 Cauchy net. -/
theorem native_cauchySeq_toLp_of_integral_sq_sub
    [Nonempty ι] [SemilatticeSup ι] {μ : Measure X} {f : ι → X → ℝ}
    (hf : ∀ a, MemLp (f a) 2 μ)
    (hC : Tendsto (fun ab : ι × ι => ∫ x, (f ab.1 x - f ab.2 x) ^ 2 ∂μ)
      atTop (𝓝 0)) :
    CauchySeq (fun a => (hf a).toLp (f a)) := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(tendsto_order.mp hC).2 (ε ^ 2) (sq_pos_of_pos hε)] with ab hab
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (dist_nonneg : 0 ≤
    dist ((hf ab.1).toLp (f ab.1)) ((hf ab.2).toLp (f ab.2)))]
  rw [dist_eq_norm]
  have hsquare := native_norm_toLp_sub_sq_eq_integral_sq (hf ab.1) (hf ab.2)
  nlinarith [norm_nonneg ((hf ab.1).toLp (f ab.1) - (hf ab.2).toLp (f ab.2))]

/-- Completeness produces a genuine L2 class, with convergence of the
original square integrals to its representative. -/
theorem native_exists_L2_limit_of_integral_sq_cauchy
    [Nonempty ι] [SemilatticeSup ι] {μ : Measure X} {f : ι → X → ℝ}
    (hf : ∀ a, MemLp (f a) 2 μ)
    (hC : Tendsto (fun ab : ι × ι => ∫ x, (f ab.1 x - f ab.2 x) ^ 2 ∂μ)
      atTop (𝓝 0)) :
    ∃ g : Lp ℝ 2 μ,
      Tendsto (fun a => (hf a).toLp (f a)) atTop (𝓝 g) ∧
      Tendsto (fun a => ∫ x, (f a x - g x) ^ 2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete
    (native_cauchySeq_toLp_of_integral_sq_sub hf hC)
  refine ⟨g, hg, ?_⟩
  have h := ((hg.sub (tendsto_const_nhds (x := g))).norm).pow 2
  simp only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  apply h.congr'
  exact Eventually.of_forall fun a => by
    have heq := native_norm_toLp_sub_sq_eq_integral_sq (hf a) (Lp.memLp g)
    simpa only [Lp.toLp_coeFn] using heq

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem native_C1_integral_mul_partial_test {Ω : Set E}
    (hΩ : IsOpen Ω) {f : E → ℝ} (hf : ContDiffOn ℝ 1 f Ω) (v : E)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, f x * fderiv ℝ φ x v) = -(∫ x in Ω, fderiv ℝ f x v * φ x) := by
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdf : ContinuousOn (fun x => fderiv ℝ f x v) Ω :=
    (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have hfirst : Integrable (fun x => fderiv ℝ φ x v * f x) := by
    apply Continuous.integrable_of_hasCompactSupport _ (hc.fderiv_apply ℝ v).mul_right
    exact (hdφ.continuousOn.mul hf.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_left.trans ((tsupport_fderiv_apply_subset ℝ v).trans hs))
  have hsecond : Integrable (fun x => φ x * fderiv ℝ f x v) := by
    apply Continuous.integrable_of_hasCompactSupport _ hc.mul_right
    exact (hφ.continuous.continuousOn.mul hdf).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_left.trans hs)
  have hprod : Integrable (fun x => φ x * f x) := by
    apply Continuous.integrable_of_hasCompactSupport _ hc.mul_right
    exact (hφ.continuous.continuousOn.mul hf.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_left.trans hs)
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hfirst hsecond hprod (fun x _ => hφ.differentiable (by simp) x)
    (fun x hx => (hf.contDiffAt (hΩ.mem_nhds (hs hx))).differentiableAt (by simp))
  have hleft : (∫ x in Ω, f x * fderiv ℝ φ x v) = ∫ x, fderiv ℝ φ x v * f x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hs (tsupport_fderiv_apply_subset ℝ v ht))), mul_zero])]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hright : (∫ x in Ω, fderiv ℝ f x v * φ x) = ∫ x, φ x * fderiv ℝ f x v := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero])]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  rw [hleft, hright, hparts, neg_neg]

/-- The original C1 function has its actual classical partial as weak
partial. No global smoothness or boundary vanishing is required. -/
theorem native_hasWeakPartialDeriv_of_contDiffOn_one {Ω : Set E}
    (hΩ : IsOpen Ω) {f : E → ℝ} (hf : ContDiffOn ℝ 1 f Ω) (i : Fin d) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) f Ω :=
  fun _ hφ hc hs => native_C1_integral_mul_partial_test hΩ hf
    (EuclideanSpace.single i 1) hφ hc hs

/-- Fixed L2 pairings are continuous along an arbitrary filter. -/
theorem native_tendsto_integral_mul_L2_filter
    {l : Filter ι} {μ : Measure X} {v : ι → Lp ℝ 2 μ} {u : Lp ℝ 2 μ}
    (hv : Tendsto v l (𝓝 u)) {ψ : X → ℝ} (hψ : MemLp ψ 2 μ) :
    Tendsto (fun a => ∫ x, v a x * ψ x ∂μ) l (𝓝 (∫ x, u x * ψ x ∂μ)) := by
  have heq (w : Lp ℝ 2 μ) : (∫ x, w x * ψ x ∂μ) = inner ℝ w (hψ.toLp ψ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with x hx
    rw [hx]
    simp [mul_comm]
  simp_rw [heq]
  exact hv.inner tendsto_const_nhds

/-- Strong L2 convergence of the actual values and actual first
derivatives preserves the weak derivative identity for a directed net. -/
theorem native_weak_partial_of_tendsto_L2_filter
    {l : Filter ι} [NeBot l] {Ω : Set E} (i : Fin d)
    {uSeq vSeq : ι → Lp ℝ 2 (volume.restrict Ω)}
    {u v : Lp ℝ 2 (volume.restrict Ω)}
    (hu : Tendsto uSeq l (𝓝 u)) (hv : Tendsto vSeq l (𝓝 v))
    (hweak : ∀ a, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i
      (vSeq a) (uSeq a) Ω) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i v u Ω := by
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 (volume.restrict Ω) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict Ω
  have hdφLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
      2 (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict Ω
  have hl := native_tendsto_integral_mul_L2_filter hu hdφLp
  have hr := (native_tendsto_integral_mul_L2_filter hv hφLp).neg
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun a =>
    (hweak a φ hφ hc hs).symm))

/-- Actual classical-gradient Cauchy estimates produce strong weak
derivatives of the same specified L2 physical limit. -/
theorem native_exists_strong_weak_partials_of_C1_cauchy
    [Nonempty ι] [SemilatticeSup ι] {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (uSeq : ι → E → ℝ) (hC1 : ∀ a, ContDiffOn ℝ 1 (uSeq a) Ω)
    (hval : ∀ a, MemLp (uSeq a) 2 (volume.restrict Ω))
    (hder : ∀ a (i : Fin d), MemLp
      (fun x => fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω))
    (hlim : Tendsto (fun a => ∫ x in Ω, (uSeq a x - u x) ^ 2) atTop (𝓝 0))
    (hgrad : Tendsto (fun ab : ι × ι => ∫ x in Ω, ∑ i : Fin d,
      (fderiv ℝ (uSeq ab.1) x (EuclideanSpace.single i 1) -
        fderiv ℝ (uSeq ab.2) x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0)) :
    Poincare.Analysis.Sobolev.Weak.MemH1 u Ω ∧
    ∃ du : Fin d → Lp ℝ 2 (volume.restrict Ω),
      (∀ i, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (du i) u Ω) ∧
      (∀ i, Tendsto (fun a => (hder a i).toLp
        (fun x => fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1)))
        atTop (𝓝 (du i))) ∧
      Tendsto (fun a => ∫ x in Ω, (uSeq a x - u x) ^ 2 + ∑ i : Fin d,
        (fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) - du i x) ^ 2) atTop (𝓝 0) := by
  classical
  have hcoord (i : Fin d) : Tendsto (fun ab : ι × ι => ∫ x in Ω,
      (fderiv ℝ (uSeq ab.1) x (EuclideanSpace.single i 1) -
        fderiv ℝ (uSeq ab.2) x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) ?_ hgrad
    intro ab
    apply integral_mono ((hder ab.1 i).sub (hder ab.2 i)).integrable_sq
      (integrable_finsetSum _ (fun j _ => ((hder ab.1 j).sub (hder ab.2 j)).integrable_sq))
    intro x
    exact Finset.single_le_sum
      (f := fun j : Fin d => (fderiv ℝ (uSeq ab.1) x (EuclideanSpace.single j 1) -
        fderiv ℝ (uSeq ab.2) x (EuclideanSpace.single j 1)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hex (i : Fin d) := native_exists_L2_limit_of_integral_sq_cauchy
    (fun a => hder a i) (hcoord i)
  choose du hduLp hduSq using hex
  have hvalue := native_tendsto_toLp_of_integral_sq_sub_filter hval hu hlim
  have hweak (i : Fin d) :
      Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (du i) u Ω := by
    have hseq (a : ι) : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i
        ((hder a i).toLp _) ((hval a).toLp _) Ω := by
      intro φ hφ hc hs
      calc
        _ = ∫ x in Ω, uSeq a x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
          apply integral_congr_ae
          filter_upwards [(hval a).coeFn_toLp] with x hx
          rw [hx]
        _ = -(∫ x in Ω, fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) * φ x) :=
          native_C1_integral_mul_partial_test hΩ (hC1 a) (EuclideanSpace.single i 1) hφ hc hs
        _ = _ := by
          congr 1
          apply integral_congr_ae
          filter_upwards [(hder a i).coeFn_toLp] with x hx
          rw [hx]
    have hw := native_weak_partial_of_tendsto_L2_filter i hvalue (hduLp i) hseq
    intro φ hφ hc hs
    calc
      _ = ∫ x in Ω, hu.toLp u x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [hu.coeFn_toLp] with x hx
        rw [hx]
      _ = _ := hw φ hφ hc hs
  refine ⟨⟨hu, fun i => ⟨du i, Lp.memLp (du i), hweak i⟩⟩, du, hweak, hduLp, ?_⟩
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hduSq i)
  have hall := hlim.add hsum
  simpa only [Finset.sum_const_zero, add_zero] using hall.congr'
    (Eventually.of_forall fun a => by
      have hvI : Integrable (fun x => (uSeq a x - u x) ^ 2) (volume.restrict Ω) :=
        ((hval a).sub hu).integrable_sq
      have hdI (i : Fin d) : Integrable (fun x =>
          (fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) - du i x) ^ 2)
          (volume.restrict Ω) := ((hder a i).sub (Lp.memLp (du i))).integrable_sq
      have hsI : Integrable (fun x => ∑ i : Fin d,
          (fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) - du i x) ^ 2)
          (volume.restrict Ω) := integrable_finsetSum Finset.univ (fun i _ => hdI i)
      symm
      calc
        _ = (∫ x in Ω, (uSeq a x - u x) ^ 2) + ∫ x in Ω, ∑ i : Fin d,
            (fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) - du i x) ^ 2 :=
          integral_add hvI hsI
        _ = _ := congrArg (fun r : ℝ => (∫ x in Ω, (uSeq a x - u x) ^ 2) + r)
          (integral_finsetSum Finset.univ (fun i _ => hdI i)))

#print axioms native_cauchySeq_toLp_of_integral_sq_sub
#print axioms native_exists_L2_limit_of_integral_sq_cauchy
#print axioms native_hasWeakPartialDeriv_of_contDiffOn_one
#print axioms native_weak_partial_of_tendsto_L2_filter
#print axioms native_exists_strong_weak_partials_of_C1_cauchy

end Yamabe3.Analysis.UniformElliptic
