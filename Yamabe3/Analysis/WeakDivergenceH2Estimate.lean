import Yamabe3.Analysis.WeakDivergenceIdentification
import Yamabe3.Analysis.WeakFlatH4Estimate
import Yamabe3.Analysis.BoundaryQuantitativeInterfaces
import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.H2Profile

/-! The fixed-coefficient smooth H2 estimate is transferred by actual
compact Sobolev approximation and operator convergence to the same weak
solution. Constants precede the solution and source. -/
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
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem sobolev_approx_error_on_subset_dimension {D : Set E} (hD : IsOpen D)
    {k l : ℕ} (hl : l ≤ k) {φ : ℕ → E → ℝ} {v : E → ℝ}
    (hφ : ∀ n, MemWkp k 2 (φ n) univ) (hv : MemWkp k 2 v univ)
    (hb : ∀ n, iteratedWeakSobolevNorm k 2 (fun x => φ n x-v x) univ ≤ sobolevApproxError n) :
    ∀ n, iteratedWeakSobolevNorm l 2 (fun x => φ n x-v x) D ≤ sobolevApproxError n := by
  intro n
  exact (wkpNorm_mono_order hl _ D).trans
    ((wkpNorm_mono_set (by norm_num) hD (subset_univ _)
      (MemWkp.sub (by norm_num) isOpen_univ (hφ n) hv)).trans (hb n))

theorem exists_weak_divergence_H2_operator_estimate
    (B : SmoothEllipticBilinearForm 3 univ)
    {V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W⊆V) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ {O : Set E} (u : E → ℝ), closure V⊆O →
      MemWkpLocally 2 u O → iteratedWeakSobolevNorm 2 2 u W ≤ C *
        (iteratedWeakSobolevNorm 0 2 u V+
          iteratedWeakSobolevNorm 0 2 (weakDivergenceSource V B.a u) V) := by
  obtain ⟨A,hA,ha⟩ := exists_derivativeProfile_two_le_source B hV hVc (subset_univ _)
    hW hWc hWV
  let J : ℝ≥0∞ := ∑ j ∈ Finset.range 3, (Fintype.card (Fin j → Fin 3) : ℝ≥0∞)
  have hJ : J≠⊤ := ENNReal.sum_ne_top.mpr (by intro j hj; simp)
  refine ⟨J*ENNReal.ofReal A, by finiteness, ?_⟩
  intro O u hVO hu
  obtain ⟨v,U,hU,hVU,hvc,hv,hvu⟩ := exists_compact_sobolev_extension_near_compact hu hVc hVO
  obtain ⟨φ,hφ,herr,-⟩ := exists_smooth_sobolev_sequence 2 hv hvc
  have hφm (n : ℕ) := (hφ n).2.2
  have hmV (n : ℕ) : MemWkp 2 2 (φ n) V := (hφm n).mono_set (by norm_num) hV (subset_univ _)
  have hvV := hv.mono_set (by norm_num : (1:ℝ≥0∞)≤2) hV (subset_univ _)
  have hmW (n : ℕ) : MemWkp 2 2 (φ n) W := (hφm n).mono_set (by norm_num) hW (subset_univ _)
  have hvW := hv.mono_set (by norm_num : (1:ℝ≥0∞)≤2) hW (subset_univ _)
  have htV : Tendsto (fun n => iteratedWeakSobolevNorm 2 2 (fun x => φ n x-v x) V) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sobolevApproxError_tendsto
      (fun _ => zero_le) (sobolev_approx_error_on_subset_dimension hV (le_refl 2) hφm hv herr)
  have htW := sobolevNorm_tendsto_of_difference hW hmW hvW
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sobolevApproxError_tendsto (fun _ => zero_le)
      (sobolev_approx_error_on_subset_dimension hW (le_refl 2) hφm hv herr))
  have ht0 := sobolevNorm_tendsto_of_difference hV
    (fun n => (hmV n).le_of_le (Nat.zero_le 2)) (hvV.le_of_le (Nat.zero_le 2))
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sobolevApproxError_tendsto (fun _ => zero_le)
      (sobolev_approx_error_on_subset_dimension hV (Nat.zero_le 2) hφm hv herr))
  obtain ⟨D,hD,hd⟩ := exists_weakDivergenceSource_difference_bound hV hVc B.a B.smooth_a
  obtain ⟨K,hK,hk⟩ := exists_weakDivergenceSource_bound hV hVc B.a B.smooth_a
  have hD0 : Tendsto (fun n => D*iteratedWeakSobolevNorm 2 2 (fun x => φ n x-v x) V) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul htV (Or.inr hD)
  have htF := sobolevNorm_tendsto_of_difference hV
    (fun n => (hk (φ n) (hmV n)).1) (hk v hvV).1
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD0 (fun _ => zero_le)
      (fun n => hd (φ n) v (hmV n) hvV))
  have htR : Tendsto (fun n => J*ENNReal.ofReal A *
      (iteratedWeakSobolevNorm 0 2 (φ n) V+
        iteratedWeakSobolevNorm 0 2 (weakDivergenceSource V B.a (φ n)) V)) atTop
      (𝓝 (J*ENNReal.ofReal A * (iteratedWeakSobolevNorm 0 2 v V+
        iteratedWeakSobolevNorm 0 2 (weakDivergenceSource V B.a v) V))) :=
    ENNReal.Tendsto.const_mul (ht0.add htF) (Or.inr (by finiteness))
  have hb (n : ℕ) : iteratedWeakSobolevNorm 2 2 (φ n) W ≤ J*ENNReal.ofReal A *
      (iteratedWeakSobolevNorm 0 2 (φ n) V+
        iteratedWeakSobolevNorm 0 2 (weakDivergenceSource V B.a (φ n)) V) := by
    let F := principalSource B.a (φ n)
    have hF : ContDiff ℝ ∞ F := contDiff_principalSource B.a B.smooth_a (hφ n).1
    have hFm : MemLp F 2 (volume.restrict V) :=
      (continuous_memLp_on_compact hF.continuous hVc).mono_measure
        (Measure.restrict_mono subset_closure le_rfl)
    have heq : ∀ ψ : E → ℝ,ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ⊆V →
        (∫ x in V,B.principalIntegrand (φ n) ψ x)=∫ x in V,F x*ψ x := by
      intro ψ hψ hc hs
      have hh := weakEquation_principalSource hV B.smooth_a (hφ n).1 ψ hψ hc hs
      convert hh using 1
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [SmoothEllipticBilinearForm.principalIntegrand, matrixFlux, partialDeriv, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [B.symm]
    have he := ha (hφ n).1 hFm heq
    have hfa : F =ᵐ[volume.restrict V] weakDivergenceSource V B.a (φ n) :=
      (weakDivergenceSource_smooth_ae hV hVc B.a B.smooth_a (hφ n).1 (hmV n)).symm
    calc
      _ ≤ J*derivativeProfile 2 W 2 (φ n) :=
        actual_weak_norm_le_local_profile hW hWc isOpen_univ (subset_univ _) (hφ n).1.contDiffOn 2
      _ ≤ J*(ENNReal.ofReal A*(derivativeProfile 2 V 0 (φ n)+derivativeProfile 2 V 0 F)) :=
        mul_le_mul le_rfl he zero_le zero_le
      _ ≤ J*(ENNReal.ofReal A*(iteratedWeakSobolevNorm 0 2 (φ n) V+iteratedWeakSobolevNorm 0 2 F V)) := by
        apply mul_le_mul le_rfl _ zero_le zero_le
        apply mul_le_mul le_rfl _ zero_le zero_le
        exact add_le_add
          (local_profile_le_actual_weak_norm hV hVc isOpen_univ (subset_univ _) (hφ n).1.contDiffOn 0)
          (local_profile_le_actual_weak_norm hV hVc isOpen_univ (subset_univ _) hF.contDiffOn 0)
      _ = _ := by rw [wkpNorm_congr_ae (k:=0) (by norm_num : (1:ℝ≥0∞)≤2) hV hfa,mul_assoc]
  have hlim := le_of_tendsto_of_tendsto' htW htR hb
  have heV : v =ᵐ[volume.restrict V] u := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact hvu (hVU (subset_closure hx))
  have heW := ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hWV) heV
  rw [wkpNorm_congr_ae (k:=2) (by norm_num) hW heW,
    wkpNorm_congr_ae (k:=0) (by norm_num : (1:ℝ≥0∞)≤2) hV heV,
    wkpNorm_congr_ae (k:=0) (by norm_num : (1:ℝ≥0∞)≤2) hV (weakDivergenceSource_congr_ae hV B.a heV)] at hlim
  exact hlim

theorem exists_weak_divergence_H2_source_estimate
    (B : SmoothEllipticBilinearForm 3 univ)
    {V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W⊆V) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ {O : Set E}, IsOpen O → closure V⊆O →
      ∀ u f : E → ℝ, MemWkp 2 2 u O → MemLp f 2 (volume.restrict O) →
      (∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
        (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
          fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,f x*φ x) →
      iteratedWeakSobolevNorm 2 2 u W ≤ C *
        (iteratedWeakSobolevNorm 0 2 u V+iteratedWeakSobolevNorm 0 2 f V) := by
  obtain ⟨C,hC,hb⟩ := exists_weak_divergence_H2_operator_estimate B hV hVc hW hWc hWV
  refine ⟨C,hC,?_⟩
  intro O hO hVO u f hu hf heq
  have hs : V⊆O := subset_closure.trans hVO
  have he := weakDivergenceSource_eq_source_ae hV hVc B.a B.smooth_a
    (hu.mono_set (by norm_num) hV hs) (hf.mono_measure (Measure.restrict_mono hs le_rfl))
    (localized_principal_restrict_canonical hV hs hu.memW1p heq)
  simpa only [wkpNorm_congr_ae (k:=0) (by norm_num : (1:ℝ≥0∞)≤2) hV he] using
    hb u hVO (locally_of_memWkp hO hu)

#print axioms exists_weak_divergence_H2_operator_estimate
#print axioms exists_weak_divergence_H2_source_estimate
end Yamabe3.Analysis.UniformElliptic
