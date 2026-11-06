/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/RicciFlow/Soliton/TwoDimensional/Compact/Gradient.lean
  PoincareLib/Geometry/Riemannian/Connection/MetricDuality.lean
  PoincareLib/Geometry/Riemannian/ScalarOperators/Divergence/Pullback.lean

Adapts the metric-duality, gradient and pullback calculations to finite regularity for
the C2 Laplacian.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.Green.NativeChartOperatorTransfer

/-! Finite regularity metric duality, gradient, Hessian trace, and chart
Laplacian transfer. The fixed Poincare source remains unchanged. These
proofs adapt its metric-duality and pullback calculations at C2 scalar
regularity, with a C1 gradient rather than assuming a smooth solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter PoincareMT VectorField Bundle
open scoped Manifold ContDiff Topology Bundle
namespace Yamabe3.Analysis.NativeC2Operators
universe u v
variable {n:ℕ} {M:Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g:RiemannianMetric n M}
lemma contMDiffAt_of_metricDual_C1 (g : RiemannianMetric n M)
    {Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 1
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) y
        (g.inner y (Z y))) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 1 (T% Z) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  let e' := trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x
  let G (y : M) := ContinuousLinearMap.inCoordinates E V (E →L[ℝ] ℝ)
    (fun y => V y →L[ℝ] ℝ) x y x y (g.inner y)
  have hG : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) 1 G x :=
    (contMDiffAt_hom_bundle _).mp ((g.contMDiff x).of_le (by simp)) |>.2
  have hGinv (y : M) (hy : y ∈ e.baseSet) (hy' : y ∈ e'.baseSet) :
      (G y).IsInvertible := by
    dsimp only [G]
    rw [ContinuousLinearMap.inCoordinates_eq hy hy']
    exact ContinuousLinearMap.isInvertible_equiv.comp
      ((g.inner_isInvertible y).comp ContinuousLinearMap.isInvertible_equiv)
  have hi := (hGinv x (FiberBundle.mem_baseSet_trivializationAt E V x)
    (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x)).contDiffAt_map_inverse (n := 1)
  have hinv := hi.contMDiffAt.comp x hG
  have hcoord := (contMDiffAt_totalSpace.mp hZ).2
  have hresult := hinv.clm_apply hcoord
  rw [contMDiffAt_section]
  apply hresult.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E V x),
    e'.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x)] with y hy hy'
  change (e ⟨y, Z y⟩).2 = (G y).inverse ((e' ⟨y, g.inner y (Z y)⟩).2)
  symm
  apply (hGinv y hy hy').inverse_apply_eq.mpr
  symm
  dsimp only [G]
  rw [ContinuousLinearMap.inCoordinates_eq hy hy']
  change (e'.continuousLinearEquivAt ℝ y hy')
    (g.inner y ((e.continuousLinearEquivAt ℝ y hy).symm
      ((e.continuousLinearEquivAt ℝ y hy) (Z y)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl
theorem contMDiffAt_gradient_C1 (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 1
      (T% (D.gradient f)) x := by
  apply contMDiffAt_of_metricDual_C1 g
  have heq (y : M) : g.inner y (D.gradient f y) = mvfderiv (𝓡 n) f y := by
    ext v
    exact D.inner_gradient f y v
  simp_rw [heq]
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  convert hf.mfderiv_const (m := 1) (by norm_num) using 1
  funext y
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv,
    NormedSpace.fromTangentSpace]
  rfl

theorem hessianOnFields_eq_inner_connection_gradient_C2 (D : LeviCivitaData g)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f x)
    (X : (y : M) → TangentSpace (𝓡 n) y)
    {Y : (y : M) → TangentSpace (𝓡 n) y}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x) :
    D.hessianOnFields f X Y x =
      g.inner x (D.connection (D.gradient f) x (X x)) (Y x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := D.metricCompatible.mvfderiv_inner_eq X
    ((contMDiffAt_gradient_C1 D hf).mdifferentiableAt (by simp)) hY
  change mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) (Y y)) x (X x) =
    g.inner x (D.connection (D.gradient f) x (X x)) (Y x) +
      g.inner x (D.gradient f x) (D.connection Y x (X x)) at h
  simp only [D.inner_gradient] at h
  exact sub_eq_iff_eq_add.mpr h

/-- The pointwise Hessian uses the same retained connection as the gradient. -/
theorem hessian_eq_inner_connection_gradient_C2 (D : LeviCivitaData g)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f x)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian f x u v = g.inner x (D.connection (D.gradient f) x u) v := by
  unfold LeviCivitaData.hessian
  rw [hessianOnFields_eq_inner_connection_gradient_C2 D hf _
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)]
  simp

theorem laplacian_eq_trace_connection_gradient_C2 (D:LeviCivitaData g)
    {f:M→ℝ} {x:M} (hf:ContMDiffAt (𝓡 n) 𝓘(ℝ,ℝ) 2 f x):
    D.laplacian f x=LinearMap.trace ℝ (TangentSpace (𝓡 n) x)
      (D.connection (D.gradient f) x).toLinearMap:=by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M→Type _) := ⟨g.toRiemannianMetric⟩
  rw [LinearMap.trace_eq_sum_inner _ (g.orthonormalBasis x)]
  unfold LeviCivitaData.laplacian
  simp_rw [hessian_eq_inner_connection_gradient_C2 D hf]
  apply Finset.sum_congr rfl
  intro i _
  exact g.symm x _ _

variable {N:Type v} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  {h:RiemannianMetric n N} {f:M→N} {x:M} {u:N→ℝ}
theorem laplacian_comp_of_metric_pullback_C2
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 u (f x)) :
    D.laplacian (u ∘ f) x = D'.laplacian u (f x) := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  have hf1 := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hf.of_le (by norm_cast : (1 : ℕ∞ω) ≤ ∞))
  have hu1 := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
  have hgrad : D.gradient (u ∘ f) =ᶠ[𝓝 x]
      mpullback (𝓡 n) (𝓡 n) f (D'.gradient u) := by
    filter_upwards [hf1, hf.continuousAt.eventually hu1, hinv, hmetric]
      with y hfy huy hiy hmy
    exact D.gradient_comp_eq_mpullback D' (hfy.mdifferentiableAt (by simp))
      (huy.mdifferentiableAt (by simp)) hiy hmy
  have hsource := (contMDiffAt_gradient_C1 D (hu.comp x (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)))).mdifferentiableAt (by simp)
  have hpull : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (mpullback (𝓡 n) (𝓡 n) f (D'.gradient u))) x := by
    apply hsource.congr_of_eventuallyEq
    filter_upwards [hgrad] with y hy
    simp only [← hy]
  have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hsource hpull (by simp) hgrad
  have htransport : (D.connection (D.gradient (u ∘ f)) x).toLinearMap =
      (mfderiv (𝓡 n) (𝓡 n) f x).inverse.toLinearMap.comp
        ((D'.connection (D'.gradient u) (f x)).toLinearMap.comp
          (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap) := by
    ext v
    change D.connection (D.gradient (u ∘ f)) x v = _
    rw [congrArg (fun L => L v) hc]
    exact D.connection_mpullback_of_metric_pullback D' hf hinv hmetric
      ((contMDiffAt_gradient_C1 D' hu).mdifferentiableAt (by simp)) v
  rw [laplacian_eq_trace_connection_gradient_C2 D (hu.comp x (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))),
    laplacian_eq_trace_connection_gradient_C2 D' hu, htransport,
    LinearMap.trace_comp_comm']
  congr 1
  ext v
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    hinv.self_of_nhds.self_apply_inverse]

#print axioms contMDiffAt_gradient_C1
#print axioms laplacian_eq_trace_connection_gradient_C2
#print axioms laplacian_comp_of_metric_pullback_C2
end Yamabe3.Analysis.NativeC2Operators
