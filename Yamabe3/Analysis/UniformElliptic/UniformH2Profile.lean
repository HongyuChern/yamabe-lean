/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/InteriorEstimates/Sobolev/H2Profile.lean

Retains the coordinate reconstruction for H2 profiles and uses a bound uniform over the
coefficient family.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.UniformElliptic.UniformInteriorHessian
import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.L2Profile

/-!
# Uniform actual H2 derivative profiles

A single constant precedes the coefficient field, smooth solution and source.
The genuine weak divergence equation identifies the actual scalar source;
explicit uniform energy bounds then reconstruct the full multilinear profile.
The reconstruction proof is adapted from the fixed upstream Sobolev/H2Profile
at PoincareLib commit 62db01af9388dc1d9b56b66d6674f4c09b2318a2 (Apache-2.0).
No upstream coefficient-dependent choice is promoted to a uniform constant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem smooth_principalSource
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (principalSource a u) := by
  apply ContDiff.neg
  apply ContDiff.sum
  intro i _
  apply contDiff_partial
  exact ContDiff.sum fun j _ => (ha i j).mul (contDiff_partial hu j)

/-- The actual smooth negative divergence is the unique weak scalar source. -/
theorem principalSource_ae_eq_of_weakEquation
    {V : Set E} (hV : IsOpen V) {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u f : E → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : WeakEquation V (matrixFlux a (fun j => partialDeriv j u)) f) :
    principalSource a u =ᵐ[volume.restrict V] f := by
  let s := principalSource a u
  have hsint : LocallyIntegrable s (volume.restrict V) :=
    (smooth_principalSource ha hu).continuous.locallyIntegrable.mono_measure Measure.restrict_le_self
  have hfint : LocallyIntegrable f (volume.restrict V) :=
    hf.continuous.locallyIntegrable.mono_measure Measure.restrict_le_self
  have hsEq := weakEquation_principalSource hV ha hu
  suffices h : (fun x => s x - f x) =ᵐ[volume.restrict V] 0 by
    filter_upwards [h] with x hx
    exact sub_eq_zero.mp hx
  change ∀ᵐ x ∂volume.restrict V, s x - f x = 0
  rw [ae_restrict_iff' hV.measurableSet]
  apply hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hsint.sub hfint))
  intro φ hφ hφc hφV
  have hid : (∫ x in V, s x * φ x) = ∫ x in V, f x * φ x :=
    (hsEq φ hφ hφc hφV).symm.trans (heq φ hφ hφc hφV)
  have hzero : ∀ x, x ∉ V → φ x • (s - f) x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hφV h))]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
  simp_rw [mul_comm (φ _)]
  rw [integral_sub (integrable_mul_test hsint hφ hφc)
    (integrable_mul_test hfint hφ hφc), hid, sub_self]

private theorem principal_equation_from_weak
    {Ω V : Set E} (B : SmoothEllipticBilinearForm d Ω) {u f : E → ℝ}
    (heq : WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u)) f) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x := by
  intro φ hφ hφc hφV
  have h := heq φ hφ hφc hφV
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SmoothEllipticBilinearForm.principalIntegrand, matrixFlux,
    partialDeriv, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [B.symm]

/-- Actual function, gradient and Hessian energies with one common constant. -/
theorem exists_uniform_h2_energy_le_source
    {Ω V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWV : closure W ⊆ V) {κ A L : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ x ∈ V, ∀ i j : Fin d, |B.a x i j| ≤ A) →
      (∀ x ∈ V, ∀ i j : Fin d, |partialDeriv i (fun y => B.a y i j) x| ≤ L) →
      (∀ x ∈ V, (∑ i : Fin d, ∑ j : Fin d,
        (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4) →
      ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
        WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u)) f →
        ((∫ x in W, u x ^ 2) + (∫ x in W, gradientSq u x) +
          (∫ x in W, hessianSq u x)) ≤
          C * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨H, hH, hHb⟩ := exists_uniform_hessian_integral_le_source
    hV hVc hVΩ hW hWc hWV hκ hA hL
  obtain ⟨G, hG, hGb⟩ := exists_uniform_gradient_integral_le_on_nested_sets
    hV (subset_closure.trans hVΩ) hW hWc hWV hκ hA
  refine ⟨1 + G + H, by positivity, ?_⟩
  intro B hB ha hDa hosc u f hu hf heq
  have hum : MemLp u 2 (volume.restrict V) :=
    (continuous_memLp_on_compact hu.continuous hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hfm : MemLp f 2 (volume.restrict V) :=
    (continuous_memLp_on_compact hf.continuous hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hsource := principalSource_ae_eq_of_weakEquation hV B.smooth_a hu hf heq
  have hsourceInt : (∫ x in V, principalSource B.a u x ^ 2) = ∫ x in V, f x ^ 2 :=
    integral_congr_ae (hsource.mono fun x hx => congrArg (fun t : ℝ => t ^ 2) hx)
  have hsecond := hHb B hB ha hDa hosc u hu
  rw [hsourceInt] at hsecond
  have hfirst := hGb B hB ha hu hum hfm (principal_equation_from_weak B heq)
  have huMono : (∫ x in W, u x ^ 2) ≤ ∫ x in V, u x ^ 2 :=
    setIntegral_mono_set hum.integrable_sq
      (Eventually.of_forall fun x => sq_nonneg (u x))
      (Eventually.of_forall (subset_closure.trans hWV))
  have hfNonneg : 0 ≤ ∫ x in V, f x ^ 2 := integral_nonneg fun x => sq_nonneg (f x)
  change (∫ x in W, gradientSq u x) ≤ _ at hfirst
  nlinarith

/-- The full genuine H2 profile has one constant chosen before every
coefficient field, solution and source satisfying the common bounds. -/
theorem exists_uniform_derivativeProfile_two_le_source
    {Ω V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWV : closure W ⊆ V) {κ A L : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ x ∈ V, ∀ i j : Fin d, |B.a x i j| ≤ A) →
      (∀ x ∈ V, ∀ i j : Fin d, |partialDeriv i (fun y => B.a y i j) x| ≤ L) →
      (∀ x ∈ V, (∑ i : Fin d, ∑ j : Fin d,
        (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4) →
      ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
        WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u)) f →
        derivativeProfile 2 W 2 u ≤ ENNReal.ofReal C *
          (derivativeProfile 2 V 0 u + derivativeProfile 2 V 0 f) := by
  obtain ⟨H, hH, hHbound⟩ := exists_uniform_h2_energy_le_source
    hV hVc hVΩ hW hWc hWV hκ hA hL
  refine ⟨((1 + d * (1 + d) : ℕ) : ℝ) * Real.sqrt H, by positivity, ?_⟩
  intro B hB ha hDa hosc u f hu hf heq
  have hfm : MemLp f 2 (volume.restrict V) :=
    (continuous_memLp_on_compact hf.continuous hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hum : MemLp u 2 (volume.restrict V) :=
    (continuous_memLp_on_compact hu.continuous hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hlocal {g : E → ℝ} (hg : Continuous g) : MemLp g 2 (volume.restrict W) :=
    (continuous_memLp_on_compact hg hWc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have huW := hlocal hu.continuous
  have hpW (i : Fin d) := hlocal (contDiff_partial hu i).continuous
  have hppW (i k : Fin d) := hlocal (contDiff_partial (contDiff_partial hu i) k).continuous
  have hgradientInt : Integrable (fun x => ∑ i : Fin d, (partialDeriv i u x) ^ 2)
      (volume.restrict W) := integrable_finsetSum _ (fun i _ => (hpW i).integrable_sq)
  have hhessianInt : Integrable
      (fun x => ∑ k : Fin d, ∑ i : Fin d, (partialDeriv k (partialDeriv i u) x) ^ 2)
      (volume.restrict W) :=
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _
      (fun i _ => (hppW i k).integrable_sq))
  have henergy := hHbound B hB ha hDa hosc hu hf heq
  dsimp only [gradientSq, hessianSq] at henergy
  have huNonneg : 0 ≤ ∫ x in W, u x ^ 2 := integral_nonneg (fun x => sq_nonneg (u x))
  have hpNonneg : 0 ≤ ∫ x in W, ∑ i : Fin d, (partialDeriv i u x) ^ 2 :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hppNonneg : 0 ≤ ∫ x in W, ∑ k : Fin d, ∑ i : Fin d,
      (partialDeriv k (partialDeriv i u) x) ^ 2 :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun k _ =>
      Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  let T : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt H) *
    (derivativeProfile 2 V 0 u + derivativeProfile 2 V 0 f)
  have huBound : derivativeProfile 2 W 0 u ≤ T := by
    simp only [T, derivativeProfile_zero]
    apply eLpNorm_two_le_of_integral_sq_le_source hum hfm huW hH
    linarith
  have hpBound (i : Fin d) : derivativeProfile 2 W 0 (partialDeriv i u) ≤ T := by
    simp only [T, derivativeProfile_zero]
    apply eLpNorm_two_le_of_integral_sq_le_source hum hfm (hpW i) hH
    have hterm : (∫ x in W, (partialDeriv i u x) ^ 2) ≤
        ∫ x in W, ∑ j : Fin d, (partialDeriv j u x) ^ 2 := by
      apply integral_mono (hpW i).integrable_sq hgradientInt
      intro x
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin d => (partialDeriv j u x) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    linarith
  have hppBound (i k : Fin d) :
      derivativeProfile 2 W 0 (partialDeriv k (partialDeriv i u)) ≤ T := by
    simp only [T, derivativeProfile_zero]
    apply eLpNorm_two_le_of_integral_sq_le_source hum hfm (hppW i k) hH
    have hterm : (∫ x in W, (partialDeriv k (partialDeriv i u) x) ^ 2) ≤
        ∫ x in W, ∑ l : Fin d, ∑ j : Fin d, (partialDeriv l (partialDeriv j u) x) ^ 2 := by
      apply integral_mono (hppW i k).integrable_sq hhessianInt
      intro x
      have hi := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin d => (partialDeriv k (partialDeriv j u) x) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have hk := Finset.single_le_sum (s := Finset.univ)
        (f := fun l : Fin d => ∑ j : Fin d, (partialDeriv l (partialDeriv j u) x) ^ 2)
        (fun l _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ k)
      simpa only [Finset.sum_apply] using hi.trans hk
    linarith
  have hpOne (i : Fin d) :
      derivativeProfile 2 W 1 (partialDeriv i u) ≤ T + ∑ _k : Fin d, T := by
    apply (derivativeProfile_succ_le_sum_partial (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      0 (contDiff_partial hu i)).trans
    exact add_le_add (hpBound i) (Finset.sum_le_sum (fun k _ => hppBound i k))
  calc
    derivativeProfile 2 W 2 u ≤ derivativeProfile 2 W 0 u +
        ∑ i : Fin d, derivativeProfile 2 W 1 (partialDeriv i u) :=
      derivativeProfile_succ_le_sum_partial (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1 hu
    _ ≤ T + ∑ _i : Fin d, (T + ∑ _k : Fin d, T) :=
      add_le_add huBound (Finset.sum_le_sum (fun i _ => hpOne i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, T,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      push_cast
      ring

#print axioms principalSource_ae_eq_of_weakEquation
#print axioms exists_uniform_h2_energy_le_source
#print axioms exists_uniform_derivativeProfile_two_le_source

end Yamabe3.Analysis.UniformElliptic
