/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/ScalarOperators/Divergence/Coordinates.lean

Adapts the smooth coordinate divergence calculation to a C2 function in dimension three.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.NativeDimensionalC2
import Yamabe3.Analysis.NativeManifoldC1Green

/-! The same retained Laplacian has its actual coordinate divergence at
C2 regularity, and hence is continuous. No fixed dependency is edited. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT VectorField Bundle
open scoped Manifold ContDiff Bundle Topology
namespace Yamabe3.Analysis.NativeC2Green
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
private theorem exists_local_chart_realization
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (heDiff : e.MDifferentiable (𝓡 n) (𝓡 n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    ∃ (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g') (V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen V ∧ x ∈ V ∧ V ⊆ e.source ∧
        ∀ y ∈ V, g'.euclideanCoefficients y = g.pullbackCoefficients e y := by
  apply RiemannianMetric.exists_local_realization e.open_source hx
    (g.pullbackCoefficients e)
  · intro y hy
    exact (g.contDiffAt_pullbackCoefficients
      ((he y hy).contMDiffAt (e.open_source.mem_nhds hy))).contDiffWithinAt
  · intro y hy v w
    exact g.symm (e y) _ _
  · intro y hy v hv
    apply g.pos (e y)
    intro hz
    apply hv
    apply heDiff.mfderiv_injective hy
    rw [map_zero]
    convert! hz using 1

/-- A smooth coordinate embedding converts the retained Laplacian to the
ordinary density divergence of the pulled-back gradient. -/
theorem density_mul_laplacian_eq_coordinate_divergence_C2
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (he' : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u : M → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ e.source)
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 u (e x)) :
    g.pullbackVolumeDensity e x * D.laplacian u (e x) =
      ∑ i, fderiv ℝ (fun y => g.pullbackVolumeDensity e y *
        WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient u) y) i) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have heDiff : e.MDifferentiable (𝓡 n) (𝓡 n) := ⟨
    fun y hy => (he y hy).mdifferentiableWithinAt (by simp),
    fun y hy => (he' y hy).mdifferentiableWithinAt (by simp)⟩
  obtain ⟨g', D', V, hVo, hxV, _, hcoeff⟩ :=
    exists_local_chart_realization (g := g) e he heDiff hx
  have hef := (he x hx).contMDiffAt (e.open_source.mem_nhds hx)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ e.source) :
      (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible := ⟨heDiff.mfderiv hy, rfl⟩
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact hi y hy
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g'.inner y a b = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y a) (mfderiv (𝓡 n) (𝓡 n) e y b) := by
    filter_upwards [hVo.mem_nhds hxV] with y hy
    have hc := hcoeff y hy
    intro a b
    rw [show g'.inner y a b = g'.euclideanCoefficients y a b by rfl, hc]
    rfl
  have hgrad : D'.gradient (u ∘ e) =ᶠ[𝓝 x]
      mpullback (𝓡 n) (𝓡 n) e (D.gradient u) := by
    have hu1 := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
      (hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
    filter_upwards [e.open_source.mem_nhds hx, hef.continuousAt.eventually hu1, hmetric]
      with y hye huy hmy
    exact D'.gradient_comp_eq_mpullback D (heDiff.mdifferentiableAt hye)
      (huy.mdifferentiableAt (by simp)) (hi y hye) hmy
  have hlap := NativeC2Operators.laplacian_comp_of_metric_pullback_C2 D' D hef hinv hmetric hu
  have hden : g'.pullbackVolumeDensity id =ᶠ[𝓝 x] g.pullbackVolumeDensity e := by
    filter_upwards [hmetric] with y hy
    unfold RiemannianMetric.pullbackVolumeDensity
    simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply]
    congr 2
    ext i j
    exact hy _ _
  rw [← hden.self_of_nhds, ← hlap,
    NativeDimensionalC2.native_density_laplacian_C2 g' D'
      (contMDiffAt_iff_contDiffAt.mp (hu.comp x (hef.of_le (by norm_cast))))]
  apply Finset.sum_congr rfl
  intro i _
  have hflux : (fun y => g'.pullbackVolumeDensity id y *
      WithLp.ofLp (D'.gradient (u ∘ e) y) i) =ᶠ[𝓝 x]
      (fun y => g.pullbackVolumeDensity e y *
        WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient u) y) i) := by
    filter_upwards [hden, hgrad] with y hyd hyg
    rw [hyd, hyg]
  exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
    L (EuclideanSpace.basisFun (Fin n) ℝ i)) hflux.fderiv_eq


theorem coordinate_gradient_C1 (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {v : M → ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : x∈e.source)
    (hv : ContMDiffAt (𝓡 n) 𝓘(ℝ,ℝ) 2 v (e x)) :
    ContDiffAt ℝ 1 (mpullback (𝓡 n) (𝓡 n) e (D.gradient v)) x := by
  have hef := he.contMDiffAt (e.open_source.mem_nhds hx)
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp),hei.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible := ⟨hD.mfderiv hx,rfl⟩
  have hgrad := (NativeC2Operators.contMDiffAt_gradient_C1 D hv).mpullback_vectorField_preimage
    (hef.of_le (by norm_cast : (2 : ℕ∞ω) ≤ ∞)) hinv (by norm_num : (1:ℕ∞ω)+1 ≤ 2)
  exact contMDiffAt_iff_contDiffAt.mp (by simpa using (Bundle.contMDiffAt_totalSpace.mp hgrad).2)

theorem continuous_laplacian_C2 (D : LeviCivitaData g) {v : M → ℝ}
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 v) : Continuous (D.laplacian v) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) z).symm
  let x := e.symm z
  have hzt : z∈e.target := mem_chart_source _ z
  have hx : x∈e.source := e.map_target hzt
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp),hei.mdifferentiableOn (by simp)⟩
  let V : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i y=>
    g.pullbackVolumeDensity e y*WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient v) y) i
  have hρ := g.contDiffAt_pullbackVolumeDensity (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)
  have hV (i) : ContDiffAt ℝ 1 (V i) x :=
    (hρ.1.of_le (by simp)).mul ((EuclideanSpace.proj i).contDiff.contDiffAt.comp x
      (coordinate_gradient_C1 D e he hei hx (hv (e x))))
  have hsum (s : Finset (Fin n)) : ContinuousAt (fun y=>∑i∈s,fderiv ℝ (V i) y (EuclideanSpace.basisFun (Fin n) ℝ i)) x := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : EuclideanSpace ℝ (Fin n)=> (0:ℝ)) x)
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (((hV i).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply continuousAt_const).add ih
  have hc : ContinuousAt (fun y=>(∑i,fderiv ℝ (V i) y (EuclideanSpace.basisFun (Fin n) ℝ i))/g.pullbackVolumeDensity e y) x :=
    (hsum Finset.univ).div hρ.1.continuousAt hρ.2.ne'

  have hl : ContinuousAt (fun y=>D.laplacian v (e y)) x := hc.congr_of_eventuallyEq (by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    have hd := density_mul_laplacian_eq_coordinate_divergence_C2 D e he hei hy (hv (e y))
    have hp := (g.contDiffAt_pullbackVolumeDensity (he.contMDiffAt (e.open_source.mem_nhds hy)) (hD.mfderiv_injective hy)).2
    apply (eq_div_iff hp.ne').mpr
    change D.laplacian v (e y)*g.pullbackVolumeDensity e y=_
    exact (mul_comm _ _).trans hd)
  have hr := hl.comp (e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hzt))
  apply hr.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hzt] with y hy
  exact congrArg (D.laplacian v) (e.right_inv hy).symm

#print axioms density_mul_laplacian_eq_coordinate_divergence_C2
#print axioms coordinate_gradient_C1
#print axioms continuous_laplacian_C2
end Yamabe3.Analysis.NativeC2Green
