/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Measure/CoordinateIntegral.lean

Uses the coordinate-density measurability calculation in the pullback argument for
singular-power integrability.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import PoincareLib.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareLib.Geometry.Riemannian.Measure.LocalFinite
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Native L6/5 integrability from actual finite coordinate power bounds

The coordinate estimate is integrated with the actual metric density.
Continuity of that density on a retained closed ball gives its upper bound.
The Euclidean power integral is transferred by the native change-of-volume
identity, and genuine local integrability is patched on the compact manifold.
Arbitrary values assigned at finitely many poles have no effect on this proof.

This is the analytic bridge used by the actual finite Green power source.
Its coordinate bounds are displayed inputs here and are constructed in the
separate Green consumer. This source is pending compilation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Analysis

open PoincareMT
local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

private theorem native_integrable_of_pullback_density
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E3 M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {F : M → ℝ} (hs : Function.support F ⊆ e.target)
    (hcoord : IntegrableOn (fun x => F (e x) * g.pullbackVolumeDensity e x) e.source) :
    Integrable F g.volumeMeasure := by
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt
  have hd : AEMeasurable (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
      (volume.restrict e.source) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable e.open_source.measurableSet
  have hρn (x : E3) : 0 ≤ g.pullbackVolumeDensity e x := Real.sqrt_nonneg _
  have hw : Integrable (fun x => F (e x))
      ((volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict
        e.source) := by
    rw [restrict_withDensity e.open_source.measurableSet]
    apply (integrable_withDensity_iff_integrable_smul₀' hd (by simp)).mpr
    simpa only [IntegrableOn, ENNReal.toReal_ofReal (hρn _),
      smul_eq_mul, mul_comm] using hcoord
  have hm := memLp_one_iff_integrable.mpr hw
  rw [← g.map_restrict_volumeMeasure_symm e he hei] at hm
  have ht := hm.comp_of_map (e.symm.continuousOn.aemeasurable e.open_target.measurableSet)
  have htarget : MemLp F 1 (g.volumeMeasure.restrict e.target) := by
    apply MemLp.ae_eq (hf_Lp := ht)
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    exact congrArg F (e.right_inv hy)
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    (memLp_one_iff_integrable.mp htarget)

/-- A real integrable coordinate power bound yields integrability on the
actual chart image, with respect to the original Riemannian volume. -/
theorem native_integrableOn_image_of_power_bound
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E3 M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {F : M → ℝ} {r C γ : ℝ} (hr : 0 < r)
    (hsource : closedBall (0 : E3) r ⊆ e.source)
    (hC : 0 ≤ C) (hγ : γ < 3)
    (hFc : ContinuousOn (fun x => F (e x)) (ball (0 : E3) r \ {0}))
    (hbound : ∀ x : E3, 0 < ‖x‖ → ‖x‖ < r →
      ‖F (e x)‖ ≤ C * ‖x‖ ^ (-γ)) :
    IntegrableOn F (e '' ball (0 : E3) r) g.volumeMeasure := by
  classical
  let ρ := g.pullbackVolumeDensity e
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn ρ (closedBall (0 : E3) r) := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hsource hx)))
      (hD.mfderiv_injective (hsource hx))).1.continuousAt.continuousWithinAt
  obtain ⟨A₀, hA₀⟩ := (isCompact_closedBall (0 : E3) r).exists_bound_of_continuousOn hρ
  let A := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hρA (x : E3) (hx : x ∈ ball (0 : E3) r) : ‖ρ x‖ ≤ A :=
    (hA₀ x (ball_subset_closedBall hx)).trans (le_max_left _ _)
  let k : E3 → ℝ := fun x => F (e x) * ρ x
  have hkc : ContinuousOn k (ball (0 : E3) r \ {0}) :=
    hFc.mul (hρ.mono (fun _ hx => ball_subset_closedBall hx.1))
  have hkmeas : AEStronglyMeasurable k (volume.restrict (ball (0 : E3) r)) := by
    have h := hkc.aestronglyMeasurable (μ := volume)
      (measurableSet_ball.diff (measurableSet_singleton (0 : E3)))
    rwa [Measure.restrict_congr_set
      (sdiff_null_ae_eq_self (measure_singleton (0 : E3)))] at h
  let f : E3 → ℝ := (ball (0 : E3) r).indicator k
  have hfmeas : AEStronglyMeasurable f volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_ball).mpr hkmeas
  have hfbound : ∀ᵐ x ∂volume.restrict (ball (0 : E3) r),
      ‖f x‖ ≤ (C * A) * ‖x‖ ^ (-γ) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : E3))] with x hx hx0
    have hxr : ‖x‖ < r := by simpa only [mem_ball, dist_zero_right] using hx
    rw [show f x = F (e x) * ρ x by simp only [f, indicator_of_mem hx, k], norm_mul]
    calc
      _ ≤ (C * ‖x‖ ^ (-γ)) * A :=
        mul_le_mul (hbound x (norm_pos_iff.mpr hx0) hxr) (hρA x hx)
          (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _))
      _ = _ := by ring
  have hfi : IntegrableOn f (ball (0 : E3) r) volume :=
    integrableOn_ball_of_norm_le_rpow (by simp) (by simpa using hγ) hfbound hfmeas
  have hfglobal : Integrable f volume :=
    hfi.integrable_of_forall_notMem_eq_zero (fun x hx => by
      simp only [f, indicator_of_notMem hx])
  let U : Set M := e '' ball (0 : E3) r
  have hUopen : IsOpen U := e.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hsource)
  let L : M → ℝ := U.indicator F
  have hsupp : Function.support L ⊆ e.target := by
    intro y hy
    have hyU : y ∈ U := by
      by_contra hn
      exact hy (by simp only [L, indicator_of_notMem hn])
    obtain ⟨x, hx, rfl⟩ := hyU
    exact e.map_source (hsource (ball_subset_closedBall hx))
  have hpull : (fun x => L (e x) * ρ x) =ᵐ[volume.restrict e.source] f := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
    have hiff : e x ∈ U ↔ x ∈ ball (0 : E3) r := by
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hxy : y = x := e.injOn (hsource (ball_subset_closedBall hy)) hx hyx
        exact hxy ▸ hy
      · intro hxb
        exact ⟨x, hxb, rfl⟩
    by_cases hxb : x ∈ ball (0 : E3) r
    · simp only [L, f, indicator_of_mem (hiff.mpr hxb), indicator_of_mem hxb, k]
    · simp only [L, f, indicator_of_notMem (mt hiff.mp hxb),
        indicator_of_notMem hxb, zero_mul]
  have hL : Integrable L g.volumeMeasure :=
    native_integrable_of_pullback_density g e he hei hsupp
      (hfglobal.integrableOn.congr hpull.symm)
  exact (integrable_indicator_iff hUopen.measurableSet).mp hL

variable [CompactSpace M]

/-- Actual finite coordinate bounds of order r^(-beta), beta<5/2,
place the same native scalar function in L6/5. No Euclidean measure is
substituted for the original volume in the result. -/
theorem native_memLp_sixFifths_of_finite_power_bounds
    (g : RiemannianMetric 3 M) (Λ : Finset M) (F : M → ℝ)
    (hFc : ContinuousOn F (Λ : Set M)ᶜ) {β : ℝ} (hβ : β < 5 / 2)
    (hlocal : ∀ p ∈ Λ, ∃ (e : OpenPartialHomeomorph E3 M) (r C : ℝ),
      e 0 = p ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      0 < r ∧ closedBall (0 : E3) r ⊆ e.source ∧ 0 ≤ C ∧
      ∀ x : E3, 0 < ‖x‖ → ‖x‖ < r →
        e x ∉ Λ ∧ ‖F (e x)‖ ≤ C * ‖x‖ ^ (-β)) :
    MemLp F (6 / 5 : ℝ≥0∞) g.volumeMeasure := by
  classical
  let K : M → ℝ := fun x => ‖F x‖ ^ (6 / 5 : ℝ)
  have hKc : ContinuousOn K (Λ : Set M)ᶜ :=
    hFc.norm.rpow_const (fun _ _ => Or.inr (by norm_num))
  have hKm : AEStronglyMeasurable F g.volumeMeasure :=
    (hFc.measurable_of_countable_compl (by
      simpa only [compl_compl] using Λ.finite_toSet.countable)).aestronglyMeasurable
  have hKI : LocallyIntegrable K g.volumeMeasure := by
    intro p
    by_cases hp : p ∈ Λ
    · obtain ⟨e, r, C, hep, he, hei, hr, hsource, hC, hdata⟩ := hlocal p hp
      have hmap : MapsTo e (ball (0 : E3) r \ {0}) (Λ : Set M)ᶜ := by
        intro x hx
        exact (hdata x (norm_pos_iff.mpr hx.2) (by simpa using hx.1)).1
      have hcoord : ContinuousOn (fun x => K (e x)) (ball (0 : E3) r \ {0}) :=
        hKc.comp (e.continuousOn.mono
          (fun _ hx => hsource (ball_subset_closedBall hx.1))) hmap
      have hbound (x : E3) (hx : 0 < ‖x‖) (hxr : ‖x‖ < r) :
          ‖K (e x)‖ ≤ C ^ (6 / 5 : ℝ) * ‖x‖ ^ (-(β * (6 / 5))) := by
        rw [show ‖K (e x)‖ = ‖F (e x)‖ ^ (6 / 5 : ℝ) by
          exact Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        calc
          _ ≤ (C * ‖x‖ ^ (-β)) ^ (6 / 5 : ℝ) :=
            Real.rpow_le_rpow (norm_nonneg _) (hdata x hx hxr).2 (by norm_num)
          _ = C ^ (6 / 5 : ℝ) * ‖x‖ ^ (-(β * (6 / 5))) := by
            rw [Real.mul_rpow hC (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
            congr 2
            ring
      have hU := e.isOpen_image_of_subset_source isOpen_ball
        (ball_subset_closedBall.trans hsource)
      refine ⟨e '' ball (0 : E3) r, hU.mem_nhds ⟨0, mem_ball_self hr, hep⟩, ?_⟩
      exact native_integrableOn_image_of_power_bound g e he hei hr hsource
        (Real.rpow_nonneg hC _) (by linarith) hcoord hbound
    · have hΩ := Λ.finite_toSet.isClosed.isOpen_compl
      have hi := hKc.integrableAt_nhdsWithin (μ := g.volumeMeasure) hΩ.measurableSet hp
      rwa [nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hp)] at hi
  have hI : Integrable K g.volumeMeasure := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hKI.integrableOn_isCompact (isCompact_univ : IsCompact (univ : Set M))
  have hpTop : (6 / 5 : ENNReal) ≠ (⊤ : ENNReal) :=
    ENNReal.div_ne_top ENNReal.ofNat_ne_top (by norm_num)
  apply (integrable_norm_rpow_iff hKm (by norm_num) hpTop).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, K] using hI

#print axioms native_integrableOn_image_of_power_bound
#print axioms native_memLp_sixFifths_of_finite_power_bounds

end Yamabe3.Analysis
