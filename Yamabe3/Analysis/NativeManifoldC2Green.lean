/-
Copyright (c) 2026 The PoincareLib contributors.
Copyright 2026 The DifferentialGeometry contributors
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Measure/Green/Chart.lean
  PoincareLib/Geometry/Riemannian/Elliptic/Dirichlet/WeakEquation.lean
Earlier source credited by PoincareLib at DifferentialGeometry 1b535dd102b94cc42b107cca27059687888f08b3.
  DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/VariationalIdentityIntegral.lean

Uses the chart and Dirichlet Green calculations for a C1 test against a C2 solution.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.NativeC2CoordinateDivergence

/-! The retained compact Green identity for a C1 test and C2 solution.
The proof uses actual coordinate integration and a finite partition; no
C-infinity upgrade or weak-equation assumption is introduced. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT VectorField Bundle
open scoped Manifold ContDiff Bundle Topology
namespace Yamabe3.Analysis.NativeC2Green
open NativeC1Green
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
private theorem apply_eq_sum_coordinates
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, L (EuclideanSpace.basisFun (Fin n) ℝ i) * v i := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    mul_comm] using h.symm

/-- The coordinate Green identity when the test function is supported inside
the chart. The integration uses the actual pulled-back metric density. -/
theorem integral_mul_laplacian_chart_density_C1_C2
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 v)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ e.target) :
    (∫ x in e.source, u (e x) * D.laplacian v (e x) * g.pullbackVolumeDensity e x) =
      -(∫ x in e.source, g.inner (e x) (D.gradient u (e x)) (D.gradient v (e x)) *
        g.pullbackVolumeDensity e x) := by
  let U := chartPullback e u
  let V : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x =>
    g.pullbackVolumeDensity e x * WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient v) x) i
  have hU : ContDiff ℝ 1 U := contDiff_chartPullback_C1 e he hu hc hs
  have hUc : HasCompactSupport U := hasCompactSupport_chartPullback e hc hs
  have hUs : tsupport U ⊆ e.source := tsupport_chartPullback_subset_source e hc hs
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv (x) (hx : x ∈ e.source) : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible :=
    ⟨hD.mfderiv hx, rfl⟩
  have hV (i) (x) (hx : x ∈ tsupport U) : ContDiffAt ℝ 1 (V i) x := by
    have hx' := hUs hx
    have hef := he.contMDiffAt (e.open_source.mem_nhds hx')
    have hρ := (g.contDiffAt_pullbackVolumeDensity hef (hD.mfderiv_injective hx')).1
    have hvec := coordinate_gradient_C1 D e he hei hx' (hv (e x))
    exact (hρ.of_le (by simp)).mul ((show EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ from EuclideanSpace.proj i).contDiff.contDiffAt.comp x hvec)

  have hparts := Poincare.integral_mul_coordinate_divergence (hU.of_le (by simp)) hUc hV
  have hleft (x) (hx : x ∈ e.source) :
      U x * ∑ i, fderiv ℝ (V i) x (EuclideanSpace.basisFun (Fin n) ℝ i) =
        u (e x) * D.laplacian v (e x) * g.pullbackVolumeDensity e x := by
    rw [show U x = u (e x) from chartPullback_apply e u hx,
      ← density_mul_laplacian_eq_coordinate_divergence_C2 D e he hei hx (hv (e x))]
    ring
  have hright (x) (hx : x ∈ e.source) :
      (∑ i, fderiv ℝ U x (EuclideanSpace.basisFun (Fin n) ℝ i) * V i x) =
        g.inner (e x) (D.gradient u (e x)) (D.gradient v (e x)) *
          g.pullbackVolumeDensity e x := by
    have hd (w : TangentSpace (𝓡 n) x) : fderiv ℝ U x w =
        mvfderiv (𝓡 n) u (e x) (mfderiv (𝓡 n) (𝓡 n) e x w) := by
      rw [(chartPullback_eventuallyEq e u hx).fderiv_eq]
      have hh := mvfderiv_comp x ((hu (e x)).mdifferentiableAt (by simp))
        (hD.mdifferentiableAt hx)
      have hh' := congrArg (fun L => L w) hh
      simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] at hh'
      exact hh'
    calc
      _ = fderiv ℝ U x (mpullback (𝓡 n) (𝓡 n) e (D.gradient v) x) *
          g.pullbackVolumeDensity e x := by
        rw [apply_eq_sum_coordinates, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [V]
        ring
      _ = _ := by
        rw [hd, mpullback,
          (hinv x hx).self_apply_inverse, D.inner_gradient]
  have hlzero (x) (hx : x ∉ e.source) :
      U x * ∑ i, fderiv ℝ (V i) x (EuclideanSpace.basisFun (Fin n) ℝ i) = 0 := by
    simp [U, chartPullback, indicator_of_notMem hx]
  have hrzero (x) (hx : x ∉ e.source) :
      (∑ i, fderiv ℝ U x (EuclideanSpace.basisFun (Fin n) ℝ i) * V i x) = 0 := by
    have hxU : x ∉ tsupport U := fun h => hx (hUs h)
    have hd : fderiv ℝ U x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hxU (tsupport_fderiv_subset ℝ h))
    simp [hd]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hlzero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hrzero] at hparts
  convert hparts using 1
  · exact setIntegral_congr_fun e.open_source.measurableSet (fun x hx => (hleft x hx).symm)
  · congr 1
    exact setIntegral_congr_fun e.open_source.measurableSet (fun x hx => (hright x hx).symm)

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

/-- Green's identity for the retained volume when the compact support lies
inside one smooth chart. -/
theorem integral_mul_laplacian_of_tsupport_subset_chart_C1_C2
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 v)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ e.target) :
    (∫ x, u x * D.laplacian v x ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient u x) (D.gradient v x) ∂g.volumeMeasure) := by
  have hl : (∫ x in e.target, u x * D.laplacian v x ∂g.volumeMeasure) =
      ∫ x, u x * D.laplacian v x ∂g.volumeMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), zero_mul]
  have hr : (∫ x in e.target, g.inner x (D.gradient u x) (D.gradient v x) ∂g.volumeMeasure) =
      ∫ x, g.inner x (D.gradient u x) (D.gradient v x) ∂g.volumeMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [D.gradient_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), map_zero]
      rfl
  rw [← hl, ← hr,
    g.integral_target_eq_integral_pullback_density e he hei
      (f := fun x => u x * D.laplacian v x)
      (hu.continuous.mul (continuous_laplacian_C2 D hv)).continuousOn,
    g.integral_target_eq_integral_pullback_density e he hei
      (continuous_inner_gradient_C1 D hu (hv.of_le (by norm_num))).continuousOn]
  exact integral_mul_laplacian_chart_density_C1_C2 D e he hei hu hv hc hs

theorem integrable_mul_laplacian_C1_C2 (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 v) (hc : HasCompactSupport u) :
    Integrable (fun x => u x * D.laplacian v x) g.volumeMeasure :=
  (hu.continuous.mul (continuous_laplacian_C2 D hv)).integrable_of_hasCompactSupport hc.mul_right

theorem integral_mul_laplacian_of_compact_C1_C2 (D : LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 h) (hfc : HasCompactSupport f) :
    (∫ x, f x * D.laplacian h x ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient f x) (D.gradient h x) ∂g.volumeMeasure) := by
  classical
  let b : ∀ x : tsupport f, SmoothBumpFunction (𝓡 n) (x : M) :=
    fun x => Classical.choice inferInstance
  let U (x : tsupport f) : Set M := interior {y | b x y = 1}
  have hcover : tsupport f ⊆ ⋃ x, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩,
      mem_interior_iff_mem_nhds.mpr (b ⟨x, hx⟩).eventuallyEq_one⟩
  obtain ⟨s, hs⟩ := hfc.isCompact.elim_finite_subcover U (fun _ => isOpen_interior) hcover
  let B : SmoothBumpCovering s (𝓡 n) M (tsupport f) :=
    { c := fun i => i.val.val
      toFun := fun i => b i.val
      c_mem' := fun i => i.val.property
      locallyFinite' := locallyFinite_of_finite _
      eventuallyEq_one' := by
        intro x hx
        obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs hx)
        exact ⟨⟨i, his⟩, mem_of_superset (isOpen_interior.mem_nhds hxi) interior_subset⟩ }
  let ρ := B.toSmoothPartitionOfUnity
  let w : s → M → ℝ := fun i x => ρ i x * f x
  have hw (i : s) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 (w i) :=
    ((ρ i).contMDiff.of_le (by simp)).mul hf
  have hwc (i : s) : HasCompactSupport (w i) := hfc.mul_left
  have hws (i : s) : tsupport (w i) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) i.val.val).source := by
    apply tsupport_mul_subset_left.trans
    exact (closure_mono (B.support_toSmoothPartitionOfUnity_subset i)).trans
      (b i.val).tsupport_subset_chartAt_source
  have hsum (x : M) : ∑ i : s, w i x = f x := by
    by_cases hx : x ∈ tsupport f
    · have hp := ρ.sum_eq_one hx
      simpa only [w, ← Finset.sum_mul, finsum_eq_sum_of_fintype, hp, one_mul] using
        congrArg (fun z : ℝ => z * f x) hp
    · simp [w, image_eq_zero_of_notMem_tsupport hx]
  have hgrad (x : M) : D.gradient f x = ∑ i : s, D.gradient (w i) x := by
    conv_lhs => rw [← funext hsum]
    exact D.gradient_finset_sum Finset.univ w x
      (fun i _ => (hw i x).mdifferentiableAt (by simp))
  have hlocal (i : s) := integral_mul_laplacian_of_tsupport_subset_chart_C1_C2 D
    (chartAt (EuclideanSpace ℝ (Fin n)) i.val.val).symm
    contMDiffOn_chart_symm contMDiffOn_chart (hw i) hh (hwc i) (hws i)
  calc
    _ = ∫ x, ∑ i : s, w i x * D.laplacian h x ∂g.volumeMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← Finset.sum_mul, hsum]
    _ = ∑ i : s, ∫ x, w i x * D.laplacian h x ∂g.volumeMeasure :=
      integral_finsetSum _ (fun i _ => integrable_mul_laplacian_C1_C2 D (hw i) hh (hwc i))
    _ = -(∑ i : s, ∫ x, g.inner x (D.gradient (w i) x) (D.gradient h x)
        ∂g.volumeMeasure) := by simp only [hlocal, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i : s, g.inner x (D.gradient (w i) x) (D.gradient h x)
        ∂g.volumeMeasure) := by
      rw [integral_finsetSum _ (fun i _ => integrable_inner_gradient_C1 D (hw i) (hh.of_le (by norm_num)) (hwc i))]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [hgrad, map_sum, sum_apply]


#print axioms integral_mul_laplacian_of_compact_C1_C2
end Yamabe3.Analysis.NativeC2Green
