/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Splitting/Busemann/Weak/StrongMaximum.lean

Uses the local Laplacian and exponential barrier arguments in a maximum principle for
the operator with a nonnegative zeroth-order coefficient.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import PoincareLib.Geometry.Riemannian.ScalarOperators.Extrema
import PoincareLib.Geometry.Riemannian.ScalarOperators.Locality
import PoincareLib.Geometry.Riemannian.ScalarOperators.Linearity
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Regularity
import Mathlib.Topology.Connected.Clopen
import PoincareLib.Geometry.Riemannian.ScalarOperators.Composition
import PoincareLib.Geometry.Riemannian.Metric.Gradient
import PoincareLib.Geometry.Manifold.ContDiff.Extension

/-!
# Native strong maximum principle with a bounded zeroth-order coefficient

This extends the pinned PoincareLib Busemann/Weak/StrongMaximum exponential
barrier proof to Delta - kappa on an arbitrary open subset of the original
manifold. Here kappa >= 0; the comparison and barrier estimates keep every
zeroth-order term. The final smooth theorem derives its upper-test condition
from the actual native Laplacian inequality, so no maximum-principle field
is an input. The open set need only be preconnected.

Proof skeleton adapted from PoincareConjecture commit
62db01af9388dc1d9b56b66d6674f4c09b2318a2, with original source unchanged.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Upper-test subharmonicity permits comparison with functions that are
smooth only on a neighborhood of the compact comparison set. -/
theorem le_on_compact_of_schrodinger_upper_tests (D : LeviCivitaData g)
    (κ : ℝ) (hκ : 0 ≤ κ) {Ω : Set M} {u : M → ℝ}
    (htest : ∀ φ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ → ∀ x ∈ Ω,
      IsLocalMax (fun y => u y - φ y) x → κ * u x ≤ D.laplacian φ x)
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hKΩ : K ⊆ Ω)
    (hu : ContinuousOn u K) {φ : M → ℝ}
    (hφ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ U)
    (hlap : ∀ x ∈ interior K, D.laplacian φ x - κ * φ x < 0)
    (hboundary : ∀ x ∈ K, x ∉ interior K → u x ≤ φ x) :
    ∀ x ∈ K, u x ≤ φ x := by
  intro x hx
  by_contra hfail
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩
    (hu.sub (hφ.continuousOn.mono hKU))
  have hpos : 0 < u q - φ q :=
    (sub_pos.mpr (lt_of_not_ge hfail)).trans_le (hmax hx)
  have hqint : q ∈ interior K := by
    by_contra hnot
    exact (not_le_of_gt hpos) (sub_nonpos.mpr (hboundary q hq hnot))
  obtain ⟨Φ, hΦ, heq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hφ (hKU hq)
  have hlocal : IsLocalMax (fun y => u y - Φ y) q := by
    filter_upwards [isOpen_interior.mem_nhds hqint, heq] with y hy hyΦ
    rw [hyΦ, heq.self_of_nhds]
    exact hmax (interior_subset hy)
  have h := htest Φ hΦ q (hKΩ hq) hlocal
  rw [D.laplacian_eq_of_eventuallyEq heq] at h
  have hmul : κ * φ q ≤ κ * u q := mul_le_mul_of_nonneg_left (by linarith) hκ
  linarith [hlap q hqint]

private theorem continuousOn_laplacian_local (D : LeviCivitaData g)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) :
    ContinuousOn (D.laplacian f) U := by
  intro x hx
  obtain ⟨F, hF, heq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hf hx
  have heq' : D.laplacian F =ᶠ[𝓝 x] D.laplacian f := by
    filter_upwards [heq.eventually_nhds] with y hy
    exact D.laplacian_eq_of_eventuallyEq hy
  exact ((D.continuous_laplacian hF).continuousAt.congr_of_eventuallyEq heq'.symm).continuousWithinAt

private theorem continuousOn_inner_gradient_local (D : LeviCivitaData g)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) :
    ContinuousOn (fun y => g.inner y (D.gradient f y) (D.gradient f y)) U := by
  intro x hx
  obtain ⟨F, hF, heq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hf hx
  have heq' : (fun y => g.inner y (D.gradient F y) (D.gradient F y)) =ᶠ[𝓝 x]
      (fun y => g.inner y (D.gradient f y) (D.gradient f y)) := by
    filter_upwards [heq.eventually_nhds] with y hy
    have hgrad : D.gradient F y = D.gradient f y := by
      unfold gradient
      rw [Poincare.mvfderiv_eq_of_eventuallyEq hy]
    rw [hgrad]
  exact ((D.continuous_inner_gradient hF hF).continuousAt.congr_of_eventuallyEq
    heq'.symm).continuousWithinAt

private theorem laplacian_exp_neg_mul_local (D : LeviCivitaData g)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U) (α : ℝ) :
    D.laplacian (fun y => Real.exp (-α * f y)) x = Real.exp (-α * f x) *
      (α ^ 2 * g.inner x (D.gradient f x) (D.gradient f x) - α * D.laplacian f x) := by
  obtain ⟨F, hF, heq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hf hx
  have hgrad : D.gradient F x = D.gradient f x := by
    unfold gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
  let e := fun r : ℝ => Real.exp (-α * r)
  have hes : ContDiff ℝ ∞ e := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hederiv (r : ℝ) : deriv e r = -α * Real.exp (-α * r) := by
    have h := (Real.hasDerivAt_exp (-α * r)).comp r ((hasDerivAt_id r).const_mul (-α))
    simpa only [e, Function.comp_def, mul_one, mul_comm] using h.deriv
  have hederiv2 (r : ℝ) : deriv (deriv e) r = α ^ 2 * Real.exp (-α * r) := by
    rw [show deriv e = fun s => -α * e s from funext hederiv]
    rw [deriv_const_mul _ (hes.differentiable (by simp) r), hederiv]
    ring
  have hl := D.laplacian_comp hF hes x
  have hexp : e ∘ F =ᶠ[𝓝 x] (fun y => Real.exp (-α * f y)) := by
    filter_upwards [heq] with y hy
    simp only [Function.comp_apply, e, hy]
  rw [D.laplacian_eq_of_eventuallyEq hexp, hederiv, hederiv2,
    heq.self_of_nhds, hgrad, D.laplacian_eq_of_eventuallyEq heq] at hl
  rw [hl]
  ring

private theorem laplacian_const_add_local (D : LeviCivitaData g)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U) (c : ℝ) :
    D.laplacian (fun y => c + f y) x = D.laplacian f x := by
  obtain ⟨F, hF, heq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hf hx
  have heq' : (fun y => c + F y) =ᶠ[𝓝 x] (fun y => c + f y) := by
    filter_upwards [heq] with y hy
    rw [hy]
  have hc : D.laplacian (fun _ : M => c) x = 0 := by
    simp [laplacian, hessian, hessianOnFields, mvfderiv_const]
  rw [← D.laplacian_eq_of_eventuallyEq heq', D.laplacian_add contMDiff_const hF,
    hc, zero_add, D.laplacian_eq_of_eventuallyEq heq]

/-- On a compact set without critical points of a smooth scalar function,
a sufficiently steep exponential satisfies Delta F - kappa F > 0. -/
theorem exists_pos_schrodinger_exp_on_compact (D : LeviCivitaData g)
    (κ : ℝ) (hκ : 0 ≤ κ) {f : M → ℝ} {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hgrad : ∀ x ∈ K, 0 < g.inner x (D.gradient f x) (D.gradient f x)) :
    ∃ α : ℝ, 0 < α ∧ ∀ x ∈ K,
      0 < D.laplacian (fun y => Real.exp (-α * f y)) x - κ * Real.exp (-α * f x) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨q, hq, hmin⟩ := hK.exists_isMinOn hne
    ((D.continuousOn_inner_gradient_local hU hf).mono hKU)
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne
    ((D.continuousOn_laplacian_local hU hf).mono hKU)
  let Q := g.inner q (D.gradient f q) (D.gradient f q)
  have hQ : 0 < Q := hgrad q hq
  let α := (|D.laplacian f p| + κ + 1) / Q + 1
  have hquot : 0 < (|D.laplacian f p| + κ + 1) / Q := div_pos (by positivity) hQ
  have hαone : 1 < α := by dsimp [α]; linarith
  have hα : 0 < α := by linarith
  have hαQ : α * Q = |D.laplacian f p| + κ + 1 + Q := by
    dsimp [α]
    rw [add_mul, div_mul_cancel₀ _ hQ.ne', one_mul]
  refine ⟨α, hα, ?_⟩
  intro x hx
  have hmin' : Q ≤ g.inner x (D.gradient f x) (D.gradient f x) := hmin hx
  have hmax' : D.laplacian f x ≤ D.laplacian f p := hmax hx
  have hmul := mul_le_mul_of_nonneg_left hmin' hα.le
  have hpositive : κ + 1 < α * g.inner x (D.gradient f x) (D.gradient f x) -
      D.laplacian f x := by linarith [le_abs_self (D.laplacian f p)]
  have hprod := mul_lt_mul_of_pos_left hpositive hα
  have hfactor : 0 < α ^ 2 * g.inner x (D.gradient f x) (D.gradient f x) -
      α * D.laplacian f x - κ := by
    nlinarith
  rw [D.laplacian_exp_neg_mul_local hU hf (hKU hx) α]
  have h := mul_pos (Real.exp_pos (-α * f x)) hfactor
  nlinarith

omit [T3Space M] [IsManifold (𝓡 n) ∞ M] in
private theorem smooth_coordinate_radius_sq
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (z : EuclideanSpace ℝ (Fin n)) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => ‖e.symm y - z‖ ^ 2) e.target := by
  have hnorm : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => ‖v - z‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  intro y hy
  exact (hnorm.contMDiff.contMDiffAt.comp y
    (hei.contMDiffAt (e.open_target.mem_nhds hy))).contMDiffWithinAt

omit [T3Space M] in
private theorem coordinate_radius_sq_gradient_pos (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (z : EuclideanSpace ℝ (Fin n)) {x : M} (hx : x ∈ e.target)
    (hne : e.symm x ≠ z) :
    0 < g.inner x (D.gradient (fun y => ‖e.symm y - z‖ ^ 2) x)
      (D.gradient (fun y => ‖e.symm y - z‖ ^ 2) x) := by
  let f := fun y => ‖e.symm y - z‖ ^ 2
  have hf := (smooth_coordinate_radius_sq e hei z).contMDiffAt
    (e.open_target.mem_nhds hx)
  apply g.pos x
  intro hzero
  have hdf : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x = 0 :=
    (g.gradient_eq_zero_iff_mfderiv_eq_zero f x).mp hzero
  let w := e.symm x
  have hw : w ∈ e.source := e.map_target hx
  have hcomp : (f ∘ e) =ᶠ[𝓝 w] (fun v => ‖v - z‖ ^ 2) := by
    filter_upwards [e.open_source.mem_nhds hw] with v hv
    simp only [Function.comp_apply, f, e.left_inv hv]
  have hew := (he.contMDiffAt (e.open_source.mem_nhds hw)).mdifferentiableAt (by simp)
  have hfx : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e w) := by
    rw [show e w = x from e.right_inv hx]
    exact hf.mdifferentiableAt (by simp)
  have hdfw : fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => ‖v - z‖ ^ 2) w = 0 := by
    rw [← hcomp.fderiv_eq, ← mfderiv_eq_fderiv, mfderiv_comp w hfx hew,
      show e w = x from e.right_inv hx, hdf]
    simp
  have hder := ((hasFDerivAt_id w).sub_const z).norm_sq
  have hz := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L (w - z))
    (hder.fderiv.symm.trans hdfw)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_apply, id_eq, zero_apply, innerSL_apply_apply] at hz
  simp only [two_smul, real_inner_self_eq_norm_sq] at hz
  have hnorm : ‖w - z‖ ^ 2 = 0 := by
    linarith
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)))

/-- A strict negative bound on an inner coordinate ball propagates throughout
an outer coordinate ball by a directly constructed exponential barrier. -/
theorem neg_on_coordinate_ball_of_neg_on_inner_ball_schrodinger (D : LeviCivitaData g)
    (κ : ℝ) (hκ : 0 ≤ κ) {Ω : Set M}
    {u : M → ℝ} (hu : ContinuousOn u Ω) (hzero : ∀ x ∈ Ω, u x ≤ 0)
    (htest : ∀ φ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ → ∀ x ∈ Ω,
      IsLocalMax (fun y => u y - φ y) x → κ * u x ≤ D.laplacian φ x)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (z : EuclideanSpace ℝ (Fin n)) {r R c : ℝ} (hr : 0 < r) (hrR : r < R)
    (hc : 0 < c) (hR : Metric.closedBall z R ⊆ e.source)
    (hRΩ : e '' Metric.closedBall z R ⊆ Ω)
    (hinner : ∀ v ∈ Metric.closedBall z r, u (e v) ≤ -c) :
    ∀ v ∈ Metric.ball z R, u (e v) < 0 := by
  let C := Metric.closedBall z R \ Metric.ball z r
  let K := e '' C
  have hC : IsCompact C := (isCompact_closedBall z R).diff Metric.isOpen_ball
  have hCs : C ⊆ e.source := fun _ hv => hR hv.1
  have hK : IsCompact K := hC.image_of_continuousOn (e.continuousOn.mono hCs)
  have hKΩ : K ⊆ Ω := (image_mono (sdiff_subset : C ⊆ Metric.closedBall z R)).trans hRΩ
  have hKU : K ⊆ e.target := by
    rintro x ⟨v, hv, rfl⟩
    exact e.map_source (hCs hv)
  let f := fun y => ‖e.symm y - z‖ ^ 2
  have hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.target :=
    smooth_coordinate_radius_sq e hei z
  have hgrad : ∀ x ∈ K, 0 < g.inner x (D.gradient f x) (D.gradient f x) := by
    rintro x ⟨v, hv, rfl⟩
    apply D.coordinate_radius_sq_gradient_pos e he hei z (e.map_source (hCs hv))
    rw [e.left_inv (hCs hv)]
    intro hvz
    exact hv.2 (by simpa [hvz] using hr)
  obtain ⟨α, hα, hαlap⟩ := D.exists_pos_schrodinger_exp_on_compact κ hκ hK e.open_target hKU hf hgrad
  let F := fun y => Real.exp (-α * f y)
  have hF : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ F e.target := by
    intro x hx
    exact Real.contDiff_exp.contMDiff.contMDiffAt.comp_contMDiffWithinAt x
      ((contMDiffWithinAt_const.mul (hf x hx)))
  let φ := fun y => c * Real.exp (-α * R ^ 2) + (-c) * F y
  have hφ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ e.target :=
    contMDiffOn_const.add (contMDiffOn_const.mul hF)
  have hφlap : ∀ x ∈ interior K, D.laplacian φ x - κ * φ x < 0 := by
    intro x hx
    have hxK := interior_subset hx
    change D.laplacian (fun y => c * Real.exp (-α * R ^ 2) + (-c) * F y) x -
      κ * (c * Real.exp (-α * R ^ 2) + (-c) * F x) < 0
    rw [D.laplacian_const_add_local (f := fun y => (-c) * F y) e.open_target
      (contMDiffOn_const.mul hF) (hKU hxK) (c * Real.exp (-α * R ^ 2)),
      D.laplacian_const_mul]
    have h := mul_neg_of_neg_of_pos (neg_neg_of_pos hc) (hαlap x hxK)
    have hnonneg : 0 ≤ κ * (c * Real.exp (-α * R ^ 2)) :=
      mul_nonneg hκ (mul_pos hc (Real.exp_pos _)).le
    dsimp [F] at h ⊢
    nlinarith
  have hboundary : ∀ x ∈ K, x ∉ interior K → u x ≤ φ x := by
    rintro x ⟨v, hv, rfl⟩ hnot
    have hvR : ‖v - z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv.1
    have hrv : r ≤ ‖v - z‖ := by
      simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hv.2
    have hvsrc := hCs hv
    have hrad : ‖v - z‖ = r ∨ ‖v - z‖ = R := by
      by_contra hfail
      have hrv' : r < ‖v - z‖ := lt_of_le_of_ne hrv (Ne.symm (not_or.mp hfail).1)
      have hvR' : ‖v - z‖ < R := lt_of_le_of_ne hvR (not_or.mp hfail).2
      let V := Metric.ball z R \ Metric.closedBall z r
      have hVopen : IsOpen V := Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
      have hVC : V ⊆ C := by
        intro w hw
        exact ⟨Metric.ball_subset_closedBall hw.1, fun hw' => hw.2 (Metric.ball_subset_closedBall hw')⟩
      have hvV : v ∈ V := by simpa [V, Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm] using And.intro hvR' hrv'
      apply hnot
      exact (e.isOpen_image_of_subset_source hVopen (hVC.trans hCs)).subset_interior_iff.mpr
        (image_mono hVC) ⟨v, hvV, rfl⟩
    have hfval : f (e v) = ‖v - z‖ ^ 2 := by simp only [f, e.left_inv hvsrc]
    rcases hrad with hrad | hrad
    · have hi : u (e v) ≤ -c := hinner v (by simp [Metric.mem_closedBall, dist_eq_norm, hrad])
      have hFle : F (e v) ≤ 1 := by
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) (sq_nonneg _))
      have hCpos : 0 < c * Real.exp (-α * R ^ 2) := mul_pos hc (Real.exp_pos _)
      dsimp [φ]
      nlinarith
    · have hφzero : φ (e v) = 0 := by dsimp [φ, F]; rw [hfval, hrad]; ring
      rw [hφzero]
      exact hzero _ (hRΩ ⟨v, hv.1, rfl⟩)
  have hcomp := D.le_on_compact_of_schrodinger_upper_tests κ hκ htest hK e.open_target hKU hKΩ
    (hu.mono hKΩ) hφ hφlap hboundary
  intro v hv
  by_cases hvr : ‖v - z‖ ≤ r
  · exact (hinner v (by simpa [Metric.mem_closedBall, dist_eq_norm] using hvr)).trans_lt (neg_neg_of_pos hc)
  have hvC : v ∈ C := ⟨Metric.ball_subset_closedBall hv,
    fun hv' => hvr (by simpa [Metric.mem_ball, dist_eq_norm] using (Metric.ball_subset_closedBall hv' : v ∈ Metric.closedBall z r))⟩
  have hvR : ‖v - z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hfval : f (e v) = ‖v - z‖ ^ 2 := by simp only [f, e.left_inv (hCs hvC)]
  have hexp : Real.exp (-α * R ^ 2) < F (e v) := by
    apply Real.exp_lt_exp.mpr
    rw [hfval]
    have hsq : ‖v - z‖ ^ 2 < R ^ 2 := sq_lt_sq₀ (norm_nonneg _) (hr.trans hrR).le |>.mpr hvR
    exact mul_lt_mul_of_neg_left hsq (neg_neg_of_pos hα)
  have hφneg : φ (e v) < 0 := by dsimp [φ]; nlinarith
  exact (hcomp (e v) ⟨v, hvC, rfl⟩).trans_lt hφneg

/-- Strict negativity at a coordinate center propagates across a coordinate
ball for a nonpositive continuous viscosity-subharmonic function. -/
theorem neg_on_coordinate_ball_schrodinger (D : LeviCivitaData g)
    (κ : ℝ) (hκ : 0 ≤ κ) {Ω : Set M} (hΩ : IsOpen Ω)
    {u : M → ℝ} (hu : ContinuousOn u Ω) (hzero : ∀ x ∈ Ω, u x ≤ 0)
    (htest : ∀ φ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ → ∀ x ∈ Ω,
      IsLocalMax (fun y => u y - φ y) x → κ * u x ≤ D.laplacian φ x)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (z : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    (hRU : Metric.closedBall z R ⊆ e.source)
    (hRΩ : e '' Metric.closedBall z R ⊆ Ω) (hz : u (e z) < 0) :
    ∀ v ∈ Metric.ball z R, u (e v) < 0 := by
  have hzU : z ∈ e.source := hRU (Metric.mem_closedBall_self hR.le)
  have hzΩ : e z ∈ Ω := hRΩ ⟨z, Metric.mem_closedBall_self hR.le, rfl⟩
  have hc : ContinuousAt (fun v => u (e v)) z :=
    (hu.continuousAt (hΩ.mem_nhds hzΩ)).comp (e.continuousAt hzU)
  have hn : {v | u (e v) < u (e z) / 2} ∈ 𝓝 z :=
    hc.preimage_mem_nhds (Iio_mem_nhds (by linarith : u (e z) < u (e z) / 2))
  obtain ⟨s, hs, hsN⟩ := Metric.mem_nhds_iff.mp hn
  let r := min s R / 2
  have hr : 0 < r := half_pos (lt_min hs hR)
  have hrs : r < s := (half_lt_self (lt_min hs hR)).trans_le (min_le_left _ _)
  have hrR : r < R := (half_lt_self (lt_min hs hR)).trans_le (min_le_right _ _)
  apply D.neg_on_coordinate_ball_of_neg_on_inner_ball_schrodinger κ hκ hu hzero htest e he hei z hr hrR
    (show 0 < -(u (e z) / 2) by linarith) hRU hRΩ
  intro v hv
  simpa only [neg_neg] using (hsN (Metric.closedBall_subset_ball hrs hv)).le

/-- Every zero of a nonpositive continuous viscosity-subharmonic function
has a coordinate neighborhood on which the function vanishes. -/
theorem zero_on_quarter_coordinate_ball_schrodinger (D : LeviCivitaData g)
    (κ : ℝ) (hκ : 0 ≤ κ) {Ω : Set M} (hΩ : IsOpen Ω)
    {u : M → ℝ} (hu : ContinuousOn u Ω) (hzero : ∀ x ∈ Ω, u x ≤ 0)
    (htest : ∀ φ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ → ∀ x ∈ Ω,
      IsLocalMax (fun y => u y - φ y) x → κ * u x ≤ D.laplacian φ x)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (z : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    (hRU : Metric.closedBall z R ⊆ e.source)
    (hRΩ : e '' Metric.closedBall z R ⊆ Ω) (hz : u (e z) = 0) :
    ∀ v ∈ Metric.ball z (R / 4), u (e v) = 0 := by
  intro v hv
  have hvR : v ∈ Metric.closedBall z R :=
    (Metric.ball_subset_closedBall ((Metric.ball_subset_ball (by linarith : R / 4 ≤ R)) hv))
  apply le_antisymm (hzero _ (hRΩ ⟨v, hvR, rfl⟩))
  by_contra hfail
  have hvneg : u (e v) < 0 := lt_of_not_ge hfail
  have hsub : Metric.closedBall v (R / 2) ⊆ Metric.closedBall z R := by
    intro w hw
    have hw' : dist w v ≤ R / 2 := hw
    have hv' : dist v z < R / 4 := hv
    have ht := dist_triangle w v z
    change dist w z ≤ R
    linarith
  have hneg := D.neg_on_coordinate_ball_schrodinger κ hκ hΩ hu hzero htest e he hei v (half_pos hR)
    (hsub.trans hRU) ((image_mono hsub).trans hRΩ) hvneg
  have hzv : z ∈ Metric.ball v (R / 2) := by
    have hv' : dist v z < R / 4 := hv
    rw [Metric.mem_ball, dist_comm]
    linarith
  have h := hneg z hzv
  rw [hz] at h
  exact lt_irrefl _ h

/-- A zero of a nonpositive native upper-test subsolution of Delta - kappa
propagates through an arbitrary open preconnected subset of the manifold. -/
theorem eq_zero_of_schrodinger_upper_tests_on (D : LeviCivitaData g)
    (κ : ℝ) (hκ : 0 ≤ κ) {Ω : Set M} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {u : M → ℝ} (hu : ContinuousOn u Ω)
    (hzero : ∀ x ∈ Ω, u x ≤ 0)
    (htest : ∀ φ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ → ∀ x ∈ Ω,
      IsLocalMax (fun y => u y - φ y) x → κ * u x ≤ D.laplacian φ x)
    {x₀ : M} (hx₀Ω : x₀ ∈ Ω) (hx₀ : u x₀ = 0) : ∀ x ∈ Ω, u x = 0 := by
  let : PreconnectedSpace Ω := Subtype.preconnectedSpace hconn
  let Z : Set Ω := {x | u x = 0}
  have hZclosed : IsClosed Z := isClosed_eq hu.domRestrict continuous_const
  have hZopen : IsOpen Z := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) (x : M)).symm
    let z := e.symm x
    have hxU : (x : M) ∈ e.target := mem_chart_source _ _
    have hzU : z ∈ e.source := e.map_target hxU
    have heΩ : e ⁻¹' Ω ∈ 𝓝 z :=
      (e.continuousAt hzU).preimage_mem_nhds (by
        rw [e.right_inv hxU]
        exact hΩ.mem_nhds x.property)
    obtain ⟨s, hs, hsU⟩ := Metric.mem_nhds_iff.mp
      (inter_mem (e.open_source.mem_nhds hzU) heΩ)
    let R := s / 2
    have hR : 0 < R := half_pos hs
    have hRUΩ : Metric.closedBall z R ⊆ e.source ∩ e ⁻¹' Ω :=
      (Metric.closedBall_subset_ball (half_lt_self hs)).trans hsU
    have hRU : Metric.closedBall z R ⊆ e.source := hRUΩ.trans inter_subset_left
    have hRΩ : e '' Metric.closedBall z R ⊆ Ω := by
      rintro y ⟨v, hv, rfl⟩
      exact (hRUΩ hv).2
    have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
    have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
    have hz : u (e z) = 0 := by rw [e.right_inv hxU]; exact hx
    have heq := D.zero_on_quarter_coordinate_ball_schrodinger κ hκ hΩ hu hzero htest
      e he hei z hR hRU hRΩ hz
    have hnM : e '' Metric.ball z (R / 4) ∈ 𝓝 (x : M) := by
      rw [← e.right_inv hxU]
      exact e.image_mem_nhds hzU (Metric.ball_mem_nhds _ (by positivity))
    have hn : ((↑) : Ω → M) ⁻¹' (e '' Metric.ball z (R / 4)) ∈ 𝓝 x :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hnM
    apply mem_of_superset hn
    rintro y ⟨v, hv, hevy⟩
    change u (y : M) = 0
    rw [← hevy]
    exact heq v hv
  have hZall : Z = univ := IsClopen.eq_univ ⟨hZclosed, hZopen⟩ ⟨⟨x₀, hx₀Ω⟩, hx₀⟩
  intro x hx
  have hz : (⟨x, hx⟩ : Ω) ∈ Z := by rw [hZall]; trivial
  exact hz
/-- The upper-test condition needed by the barrier theorem follows from
an actual smooth native Laplacian inequality. -/
theorem eq_zero_of_nonpos_laplacian_ge_mul_on (D : LeviCivitaData g)
    (κ : ℝ) (hκ : 0 ≤ κ) {Ω : Set M} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u Ω)
    (hzero : ∀ x ∈ Ω, u x ≤ 0)
    (hlap : ∀ x ∈ Ω, κ * u x ≤ D.laplacian u x)
    {x₀ : M} (hx₀Ω : x₀ ∈ Ω) (hx₀ : u x₀ = 0) : ∀ x ∈ Ω, u x = 0 := by
  apply D.eq_zero_of_schrodinger_upper_tests_on κ hκ hΩ hconn hu.continuousOn hzero
    _ hx₀Ω hx₀
  intro φ hφ x hx hmax
  obtain ⟨U, hU, heq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hΩ hu hx
  have hmaxU : IsLocalMax (fun y => U y - φ y) x := by
    filter_upwards [hmax, heq] with y hy hyU
    rw [hyU, heq.self_of_nhds]
    exact hy
  have h := D.laplacian_nonpos_of_isLocalMax (hU.sub hφ) hmaxU
  rw [D.laplacian_sub hU hφ, D.laplacian_eq_of_eventuallyEq heq] at h
  linarith [hlap x hx]

/-- Native strong minimum principle for a nonnegative smooth function with
Delta u <= kappa u on an open preconnected set. -/
theorem eq_zero_of_nonneg_laplacian_le_mul_on (D : LeviCivitaData g)
    (κ : ℝ) (hκ : 0 ≤ κ) {Ω : Set M} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u Ω)
    (hzero : ∀ x ∈ Ω, 0 ≤ u x)
    (hlap : ∀ x ∈ Ω, D.laplacian u x ≤ κ * u x)
    {x₀ : M} (hx₀Ω : x₀ ∈ Ω) (hx₀ : u x₀ = 0) : ∀ x ∈ Ω, u x = 0 := by
  have hneg : ∀ x ∈ Ω, (-u x) = 0 := by
    apply D.eq_zero_of_nonpos_laplacian_ge_mul_on κ hκ hΩ hconn hu.neg
      (fun x hx => neg_nonpos.mpr (hzero x hx)) _ hx₀Ω (by rw [hx₀, neg_zero])
    intro x hx
    change κ * (-u x) ≤ D.laplacian (fun y => -u y) x
    have heq : (fun y => -u y) = (fun y => (-1 : ℝ) * u y) := by
      funext y
      ring
    rw [heq, D.laplacian_const_mul]
    linarith [hlap x hx]
  intro x hx
  exact neg_eq_zero.mp (hneg x hx)

/-- One positive value propagates throughout an open preconnected set for
a nonnegative smooth native subsolution of -Delta + kappa. -/
theorem pos_of_nonneg_laplacian_le_mul_on (D : LeviCivitaData g)
    (κ : ℝ) (hκ : 0 ≤ κ) {Ω : Set M} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u Ω)
    (hzero : ∀ x ∈ Ω, 0 ≤ u x)
    (hlap : ∀ x ∈ Ω, D.laplacian u x ≤ κ * u x)
    (hpos : ∃ x ∈ Ω, 0 < u x) : ∀ x ∈ Ω, 0 < u x := by
  intro x hx
  by_contra hfail
  have hux : u x = 0 := le_antisymm (le_of_not_gt hfail) (hzero x hx)
  have hident := D.eq_zero_of_nonneg_laplacian_le_mul_on κ hκ hΩ hconn hu hzero hlap hx hux
  obtain ⟨y, hy, hupy⟩ := hpos
  rw [hident y hy] at hupy
  exact lt_irrefl _ hupy

/-- On a compact background the continuous variable potential supplies its
own upper bound. There is no assumed maximum principle or bound in this
native strict-positivity theorem. The open subset itself may be noncompact. -/
theorem pos_of_nonneg_schrodinger_on [CompactSpace M] (D : LeviCivitaData g)
    {Ω : Set M} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (V : M → ℝ) (hV : Continuous V) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u Ω)
    (hzero : ∀ x ∈ Ω, 0 ≤ u x)
    (hlap : ∀ x ∈ Ω, D.laplacian u x ≤ V x * u x)
    (hpos : ∃ x ∈ Ω, 0 < u x) : ∀ x ∈ Ω, 0 < u x := by
  obtain ⟨C, hC⟩ := (HasCompactSupport.of_compactSpace V).exists_bound_of_continuous hV
  let κ : ℝ := max C 0
  have hκ : 0 ≤ κ := le_max_right _ _
  apply D.pos_of_nonneg_laplacian_le_mul_on κ hκ hΩ hconn hu hzero _ hpos
  intro x hx
  apply (hlap x hx).trans
  apply mul_le_mul_of_nonneg_right _ (hzero x hx)
  have hCV : |V x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x
  exact (le_abs_self (V x)).trans (hCV.trans (le_max_left C 0))

#print axioms le_on_compact_of_schrodinger_upper_tests
#print axioms exists_pos_schrodinger_exp_on_compact
#print axioms eq_zero_of_schrodinger_upper_tests_on
#print axioms eq_zero_of_nonneg_laplacian_le_mul_on
#print axioms pos_of_nonneg_schrodinger_on

end PoincareMT.LeviCivitaData
