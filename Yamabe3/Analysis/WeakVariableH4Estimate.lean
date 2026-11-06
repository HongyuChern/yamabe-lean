import Yamabe3.Analysis.WeakDivergencePotentialContinuity
import Yamabe3.Analysis.WeakFlatH4Estimate

/-! Uniform interior H4 estimates for the actual weak variable-coefficient
operator. The bound precedes its elliptic coefficient form, signed
potential and input function; smooth approximants use their own actual
operator sources and converge in H2. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_weak_variable_H4_estimate
    {Ω V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V⊆Ω)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V)
    {κ L Q : ℝ} (hκ : 0<κ) (hL : 0≤L) (hQ : 0 ≤ Q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀B : Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm 3 Ω,κ≤B.lam →
      (∀n≤4,∀x∈V,∀i j : Fin 3,‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖≤L) →
      (∀x∈V,(∑i : Fin 3,∑j : Fin 3,(B.a x i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j)^2)≤1/4) →
      ∀ q : E → ℝ, ContDiff ℝ ∞ q →
      (∀ n ≤ 2, ∀ x ∈ V, ‖iteratedFDeriv ℝ n q x‖ ≤ Q) →
      ∀ {O : Set E} (u : E → ℝ), closure V ⊆ O → MemWkpLocally 4 u O →
      iteratedWeakSobolevNorm 4 2 u W ≤ C *
        (iteratedWeakSobolevNorm 0 2 u V + iteratedWeakSobolevNorm 2 2 (weakDivergencePotential V B.a q u) V) := by
  obtain ⟨A,hA,ha⟩ := exists_local_uniform_derivativeProfile_add_two_with_potential
    2 isOpen_univ hV hVc (subset_univ _) (Ω := Ω) hVΩ
    hW hWc hWV (κ := κ) (L := L) (Q := Q) hκ hL hQ
  let J : ℝ≥0∞ := ∑ j ∈ Finset.range 5, (Fintype.card (Fin j → Fin 3) : ℝ≥0∞)
  have hJ : J ≠ ⊤ := ENNReal.sum_ne_top.mpr (by intro j hj; simp)
  refine ⟨J*ENNReal.ofReal A, by finiteness, ?_⟩
  intro B hBell hjet hosc q hq hqj O u hVO hu
  obtain ⟨v,U,hU,hVU,hvc,hv,hvu⟩ := exists_compact_sobolev_extension_near_compact hu hVc hVO
  obtain ⟨φ,hφ,herr,-⟩ := exists_smooth_sobolev_sequence 4 hv hvc
  have hφm (n : ℕ) := (hφ n).2.2
  have hmV (n : ℕ) : MemWkp 4 2 (φ n) V := (hφm n).mono_set (by norm_num) hV (subset_univ _)
  have hvV := hv.mono_set (by norm_num : (1:ℝ≥0∞) ≤ 2) hV (subset_univ _)
  have hmW (n : ℕ) : MemWkp 4 2 (φ n) W := (hφm n).mono_set (by norm_num) hW (subset_univ _)
  have hvW := hv.mono_set (by norm_num : (1:ℝ≥0∞) ≤ 2) hW (subset_univ _)
  have hbV := sobolev_approx_error_on_subset hV (le_refl 4) hφm hv herr
  have htV : Tendsto (fun n => iteratedWeakSobolevNorm 4 2 (fun x => φ n x-v x) V) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sobolevApproxError_tendsto (fun _ => zero_le) hbV
  have htW := sobolevNorm_tendsto_of_difference hW hmW hvW
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sobolevApproxError_tendsto (fun _ => zero_le)
      (sobolev_approx_error_on_subset hW (le_refl 4) hφm hv herr))
  have ht0 := sobolevNorm_tendsto_of_difference hV
    (fun n => (hmV n).le_of_le (Nat.zero_le 4)) (hvV.le_of_le (Nat.zero_le 4))
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sobolevApproxError_tendsto (fun _ => zero_le)
      (sobolev_approx_error_on_subset hV (Nat.zero_le 4) hφm hv herr))
  obtain ⟨D,hD,hb⟩ := exists_weakDivergencePotential_difference_bound 2 hV hVc B.a B.smooth_a q hq
  obtain ⟨M,hM,hmem⟩ := exists_weakDivergencePotential_bound 2 hV hVc B.a B.smooth_a q hq
  have hB0 : Tendsto (fun n => D*iteratedWeakSobolevNorm 4 2 (fun x => φ n x-v x) V) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul htV (Or.inr hD)
  have htF := sobolevNorm_tendsto_of_difference hV
    (fun n => (hmem (φ n) (hmV n)).1) (hmem v hvV).1
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB0 (fun _ => zero_le)
      (fun n => hb (φ n) v (hmV n) hvV))
  have hJn : J*ENNReal.ofReal A ≠ ⊤ := by finiteness
  have htR : Tendsto (fun n => J*ENNReal.ofReal A *
      (iteratedWeakSobolevNorm 0 2 (φ n) V + iteratedWeakSobolevNorm 2 2 (weakDivergencePotential V B.a q (φ n)) V)) atTop
      (𝓝 (J*ENNReal.ofReal A * (iteratedWeakSobolevNorm 0 2 v V +
        iteratedWeakSobolevNorm 2 2 (weakDivergencePotential V B.a q v) V))) :=
    ENNReal.Tendsto.const_mul (ht0.add htF) (Or.inr hJn)
  have hbnd (n : ℕ) : iteratedWeakSobolevNorm 4 2 (φ n) W ≤ J*ENNReal.ofReal A *
      (iteratedWeakSobolevNorm 0 2 (φ n) V + iteratedWeakSobolevNorm 2 2 (weakDivergencePotential V B.a q (φ n)) V) := by
    let F : E → ℝ := fun x => principalSource B.a (φ n) x-q x*φ n x
    have hF : ContDiff ℝ ∞ F :=
      (contDiff_principalSource B.a B.smooth_a (hφ n).1).sub (hq.mul (hφ n).1)
    have heq : WeakEquation V (matrixFlux B.a (fun j => partialDeriv j (φ n)))
        (fun x => F x+q x*φ n x) := by
      have h := weakEquation_principalSource hV B.smooth_a (hφ n).1
      simpa only [F,sub_add_cancel] using h
    have he := ha B hBell hjet hosc q hq.contDiffOn hqj
      (hφ n).1.contDiffOn hF.contDiffOn heq
    have hfa : F =ᵐ[volume.restrict V] weakDivergencePotential V B.a q (φ n) := by
      filter_upwards [weakDivergenceSource_smooth_ae hV hVc B.a B.smooth_a (hφ n).1
        ((hmV n).le_of_le (by norm_num : 2≤4))] with x hx
      exact congrArg (fun t => t-q x*φ n x) hx.symm
    calc
      _ ≤ J*derivativeProfile 2 W 4 (φ n) :=
        actual_weak_norm_le_local_profile hW hWc isOpen_univ (subset_univ _) (hφ n).1.contDiffOn 4
      _ ≤ J*(ENNReal.ofReal A*(derivativeProfile 2 V 0 (φ n)+derivativeProfile 2 V 2 F)) :=
        mul_le_mul le_rfl he zero_le zero_le
      _ ≤ J*(ENNReal.ofReal A*(iteratedWeakSobolevNorm 0 2 (φ n) V+iteratedWeakSobolevNorm 2 2 F V)) := by
        apply mul_le_mul le_rfl _ zero_le zero_le
        apply mul_le_mul le_rfl _ zero_le zero_le
        exact add_le_add
          (local_profile_le_actual_weak_norm hV hVc isOpen_univ (subset_univ _) (hφ n).1.contDiffOn 0)
          (local_profile_le_actual_weak_norm hV hVc isOpen_univ (subset_univ _) hF.contDiffOn 2)
      _ = _ := by rw [wkpNorm_congr_ae (k := 2) (by norm_num) hV hfa, mul_assoc]
  have hlim := le_of_tendsto_of_tendsto' htW htR hbnd
  have heV : v =ᵐ[volume.restrict V] u := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact hvu (hVU (subset_closure hx))
  have heW := ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hWV) heV
  rw [wkpNorm_congr_ae (k := 4) (by norm_num) hW heW,
    wkpNorm_congr_ae (k := 0) (by norm_num) hV heV,
    wkpNorm_congr_ae (k := 2) (by norm_num) hV (weakDivergencePotential_congr_ae hV B.a q heV)] at hlim
  exact hlim

#print axioms exists_uniform_weak_variable_H4_estimate
end Yamabe3.Analysis.UniformElliptic
