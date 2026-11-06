import Yamabe3.Analysis.UniformElliptic.UniformDivergenceHessian
import Yamabe3.Analysis.UniformElliptic.UniformCaccioppoli

/-!
# Genuine uniform local H2 energy from common coefficient bounds

One constant is selected from fixed nested sets and numerical coefficient
bounds before the coefficient field and the solution. The proof combines the
explicit global perturbative Hessian estimate, an actual cutoff and the
uniform Caccioppoli bound. The scalar forcing is the genuine negative
coordinate divergence, so no weak equation or regularity is a free field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
open Poincare.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem memLp_continuous_on_compact {u : E → ℝ} (hu : Continuous u)
    {K : Set E} (hK : IsCompact K) : MemLp u 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := hK.bddAbove_image hu.continuousOn.norm
  apply MemLp.of_bound hu.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC (mem_image_of_mem _ hx)

omit [NeZero d] in
private theorem contDiff_principalSource
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (principalSource a u) := by
  apply ContDiff.neg
  apply ContDiff.sum
  intro i _
  apply contDiff_partial
  exact ContDiff.sum fun j _ => (ha i j).mul (contDiff_partial hu j)

omit [NeZero d] in
private theorem hessianSq_eq_of_eventuallyEq {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) : hessianSq u x = hessianSq v x := by
  have hp (j : Fin d) : partialDeriv j u =ᶠ[𝓝 x] partialDeriv j v := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single j 1)) hy
  unfold hessianSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs := congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) (hp j).fderiv_eq
  exact congrArg (fun t : ℝ => t ^ 2) hs

omit [NeZero d] in
private theorem cutoff_energy_bound {η : E → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ∃ N : ℝ, 0 ≤ N ∧ (∀ x, gradientSq η x ≤ N) ∧ (∀ x, hessianSq η x ≤ N) := by
  have hg : HasCompactSupport (gradientSq η) := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    by_contra hnot
    apply hx
    simp [gradientSq, partialDeriv, fderiv_of_notMem_tsupport ℝ hnot]
  have hh : HasCompactSupport (hessianSq η) := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    by_contra hnot
    apply hx
    simp [hessianSq, second_partial_eq_zero_of_notMem_tsupport hnot]
  obtain ⟨N₁, hN₁⟩ := hg.exists_bound_of_continuous (continuous_gradientSq hη)
  obtain ⟨N₂, hN₂⟩ := hh.exists_bound_of_continuous (continuous_hessianSq hη)
  refine ⟨max 0 (max N₁ N₂), le_max_left _ _, ?_, ?_⟩
  · intro x
    exact (le_abs_self _).trans ((hN₁ x).trans ((le_max_left _ _).trans (le_max_right _ _)))
  · intro x
    exact (le_abs_self _).trans ((hN₂ x).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- The genuine local Hessian energy estimate is uniform over all smooth
coefficient arrays obeying the displayed common bounds. C is chosen before
B and u. The only source appearing is the actual negative divergence. -/
theorem exists_uniform_hessian_integral_le_source
    {Ω V U : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUV : closure U ⊆ V) {κ A L : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ x ∈ V, ∀ i j : Fin d, |B.a x i j| ≤ A) →
      (∀ x ∈ V, ∀ i j : Fin d, |partialDeriv i (fun y => B.a y i j) x| ≤ L) →
      (∀ x ∈ V, (∑ i : Fin d, ∑ j : Fin d,
        (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4) →
      ∀ u : E → ℝ, ContDiff ℝ ∞ u →
        (∫ x in U, hessianSq u x) ≤ C *
          ((∫ x in V, u x ^ 2) + ∫ x in V, principalSource B.a u x ^ 2) := by
  obtain ⟨W, hW, hUW, hWV⟩ := hUc.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hUV)
  have hWc : IsCompact (closure W) := hVc.of_isClosed_subset isClosed_closure
    (hWV.trans subset_closure)
  have hWV' : W ⊆ V := subset_closure.trans hWV
  obtain ⟨G, hG, hGbound⟩ := exists_uniform_gradient_integral_le_on_nested_sets
    hV (subset_closure.trans hVΩ) hW hWc hWV hκ hA
  obtain ⟨η, hη, hηc, hηrange, hηone, hηW⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hUc hW hUW
  obtain ⟨N, hN, hgη, hhη⟩ := cutoff_energy_bound hη hηc
  let K : ℝ := cutoffSourceEnergyConstant d A L N
  have hK : 0 ≤ K := cutoffSourceEnergyConstant_nonneg d A L N
  refine ⟨4 * K * (G + 1), by positivity, ?_⟩
  intro B hB ha hDa hosc u hu
  let f := principalSource B.a u
  have hfc : Continuous f := (contDiff_principalSource B.smooth_a hu).continuous
  have hum : MemLp u 2 (volume.restrict V) :=
    (memLp_continuous_on_compact hu.continuous hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hfm : MemLp f 2 (volume.restrict V) :=
    (memLp_continuous_on_compact hfc hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hgrad := hGbound B hB ha hu hum hfm
    (principal_equation_of_smooth B hV hu)
  have huintW := hum.integrable_sq.mono_measure (Measure.restrict_mono hWV' le_rfl)
  have hfintW := hfm.integrable_sq.mono_measure (Measure.restrict_mono hWV' le_rfl)
  have hgintW : Integrable (gradientSq u) (volume.restrict W) :=
    (continuous_gradientSq hu).continuousOn.integrableOn_compact hWc |>.mono_set subset_closure
  let v : E → ℝ := fun x => η x * u x
  have hv : ContDiff ℝ ∞ v := hη.mul hu
  have hvc : HasCompactSupport v := hηc.mul_right
  have hvs : tsupport v ⊆ W := tsupport_mul_subset_left.trans hηW
  have hglobal := principal_hessian_energy_le_four (fun i j => (B.smooth_a i j).continuous)
    hv hvc (fun x hx => hosc x (hWV' (hvs hx)))
  have hS : Integrable (fun x => principalPart B.a v x ^ 2) volume :=
    integrable_principalPart_sq (fun i j => (B.smooth_a i j).continuous) hv hvc
  have hzero (x : E) (hx : x ∉ W) : principalPart B.a v x ^ 2 = 0 := by
    have hxv : x ∉ tsupport v := fun h => hx (hvs h)
    simp [principalPart, second_partial_eq_zero_of_notMem_tsupport hxv]
  have hlocal : (∫ x, principalPart B.a v x ^ 2) ≤
      K * ((∫ x in W, f x ^ 2) + (∫ x in W, u x ^ 2) + ∫ x in W, gradientSq u x) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      ← integral_add hfintW huintW,
      ← integral_add (f := fun x => f x ^ 2 + u x ^ 2) (g := gradientSq u)
        (hfintW.add huintW) hgintW, ← integral_const_mul]
    apply setIntegral_mono_on hS.restrict
      (((hfintW.add huintW).add hgintW).const_mul K) hW.measurableSet
    intro x hx
    have hηx : |η x| ≤ 1 := by
      have h := hηrange (mem_range_self x)
      rw [abs_of_nonneg h.1]
      exact h.2
    change principalPart B.a (fun y => η y * u y) x ^ 2 ≤
      cutoffSourceEnergyConstant d A L N *
        (principalSource B.a u x ^ 2 + u x ^ 2 + gradientSq u x)
    exact principalPart_cutoff_sq_le_divergence_source B.smooth_a hη hu x hA hL hN
      (ha x (hWV' hx)) (hDa x (hWV' hx)) hηx (hgη x) (hhη x)
  have hUeq : (∫ x in U, hessianSq u x) = ∫ x in U, hessianSq v x := by
    apply setIntegral_congr_fun hU.measurableSet
    intro x hx
    apply hessianSq_eq_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    simp only [v, hηone y (subset_closure hy), one_mul]
  have htotal : (∫ x in U, hessianSq u x) ≤ 4 * K *
      ((∫ x in W, f x ^ 2) + (∫ x in W, u x ^ 2) + ∫ x in W, gradientSq u x) := by
    rw [hUeq]
    apply (setIntegral_le_integral (integrable_hessianSq hv hvc)
      (Eventually.of_forall (hessianSq_nonneg v))).trans
    apply hglobal.trans
    calc
      _ ≤ 4 * (K * ((∫ x in W, f x ^ 2) + (∫ x in W, u x ^ 2) +
          ∫ x in W, gradientSq u x)) := mul_le_mul_of_nonneg_left hlocal (by norm_num)
      _ = _ := by ring
  have huMono : (∫ x in W, u x ^ 2) ≤ ∫ x in V, u x ^ 2 :=
    setIntegral_mono_set hum.integrable_sq (Eventually.of_forall fun x => sq_nonneg (u x))
      (Eventually.of_forall hWV')
  have hfMono : (∫ x in W, f x ^ 2) ≤ ∫ x in V, f x ^ 2 :=
    setIntegral_mono_set hfm.integrable_sq (Eventually.of_forall fun x => sq_nonneg (f x))
      (Eventually.of_forall hWV')
  apply htotal.trans
  calc
    _ ≤ 4 * K * ((∫ x in V, f x ^ 2) + (∫ x in V, u x ^ 2) +
        G * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (add_le_add hfMono huMono) hgrad
    _ = _ := by dsimp [f]; ring

#print axioms exists_uniform_hessian_integral_le_source

end Yamabe3.Analysis.UniformElliptic
