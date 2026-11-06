/-
Copyright (c) 2026 The PoincareLib contributors.
Copyright 2026 The DifferentialGeometry contributors
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Measure/Green/Chart.lean
  PoincareLib/Geometry/Riemannian/Measure/Green/ChartSupport.lean
  PoincareLib/Geometry/Riemannian/Elliptic/Dirichlet/WeakEquation.lean
  PoincareLib/Geometry/Riemannian/Connection/MetricDuality.lean
Earlier source credited by PoincareLib at DifferentialGeometry 1b535dd102b94cc42b107cca27059687888f08b3.
  DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/VariationalIdentityIntegral.lean

Adapts the coordinate Green calculation to C1 compact tests, and uses local metric-
duality and Dirichlet weak-equation arguments.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.NativeManifoldOperatorC2
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.WeakEquation

/-! C1 compact tests against the genuine smooth Laplacian. Adapted from
fixed Poincare ChartSupport, Green.Chart and Dirichlet.WeakEquation proofs;
only the project copy is changed. No smoothing hypothesis is inserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT VectorField Bundle
open scoped Manifold ContDiff Topology Bundle
namespace Yamabe3.Analysis.NativeC1Green
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
lemma contMDiffAt_of_metricDual_C0 (g : RiemannianMetric n M)
    {Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 0
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) y
        (g.inner y (Z y))) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 0 (T% Z) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  let e' := trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x
  let G (y : M) := ContinuousLinearMap.inCoordinates E V (E →L[ℝ] ℝ)
    (fun y => V y →L[ℝ] ℝ) x y x y (g.inner y)
  have hG : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) 0 G x :=
    (contMDiffAt_hom_bundle _).mp ((g.contMDiff x).of_le (by simp)) |>.2
  have hGinv (y : M) (hy : y ∈ e.baseSet) (hy' : y ∈ e'.baseSet) :
      (G y).IsInvertible := by
    dsimp only [G]
    rw [ContinuousLinearMap.inCoordinates_eq hy hy']
    exact ContinuousLinearMap.isInvertible_equiv.comp
      ((g.inner_isInvertible y).comp ContinuousLinearMap.isInvertible_equiv)
  have hi := (hGinv x (FiberBundle.mem_baseSet_trivializationAt E V x)
    (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x)).contDiffAt_map_inverse (n := 0)
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
theorem contMDiffAt_gradient_C0 (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1 f x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 0
      (T% (D.gradient f)) x := by
  apply contMDiffAt_of_metricDual_C0 g
  have heq (y : M) : g.inner y (D.gradient f y) = mvfderiv (𝓡 n) f y := by
    ext v
    exact D.inner_gradient f y v
  simp_rw [heq]
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  convert hf.mfderiv_const (m := 0) (by norm_num) using 1
  funext y
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv,
    NormedSpace.fromTangentSpace]
  rfl

theorem continuous_inner_gradient_C1 (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 v) :
    Continuous (fun x => g.inner x (D.gradient u x) (D.gradient v x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have h := (((g.contMDiff x).of_le (show (0:ℕ∞ω) ≤ ∞ by simp)).clm_bundle_apply
    (contMDiffAt_gradient_C0 D (hu x))).clm_bundle_apply
      (contMDiffAt_gradient_C0 D (hv x))
  exact ((contMDiffAt_totalSpace.mp h).2).continuousAt

theorem contDiff_chartPullback_C1
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) {u : M → ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 u)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ e.target) :
    ContDiff ℝ 1 (chartPullback e u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ e.source
  · apply ContDiffAt.congr_of_eventuallyEq _ (chartPullback_eventuallyEq e u hx)
    exact ((hu (e x)).comp x ((he.contMDiffAt (e.open_source.mem_nhds hx)).of_le (by simp))).contDiffAt
  · have hx' : x ∉ tsupport (chartPullback e u) :=
      fun h => hx (tsupport_chartPullback_subset_source e hc hs h)
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const
      (notMem_tsupport_iff_eventuallyEq.mp hx')
private theorem apply_eq_sum_coordinates
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, L (EuclideanSpace.basisFun (Fin n) ℝ i) * v i := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    mul_comm] using h.symm

/-- The coordinate Green identity when the test function is supported inside
the chart. The integration uses the actual pulled-back metric density. -/
theorem integral_mul_laplacian_chart_density_C1
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
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
    have hgrad := (D.contMDiffAt_gradient (hv (e x))).mpullback_vectorField_preimage
      hef (hinv x hx') (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
    have hvec : ContDiffAt ℝ ∞ (mpullback (𝓡 n) (𝓡 n) e (D.gradient v)) x := by
      exact contMDiffAt_iff_contDiffAt.mp (by simpa using (Bundle.contMDiffAt_totalSpace.mp hgrad).2)
    exact (hρ.mul ((EuclideanSpace.proj i).contDiff.contDiffAt.comp x hvec)).of_le
      (by norm_cast : (1 : ℕ∞ω) ≤ ∞)
  have hparts := Poincare.integral_mul_coordinate_divergence (hU.of_le (by simp)) hUc hV
  have hleft (x) (hx : x ∈ e.source) :
      U x * ∑ i, fderiv ℝ (V i) x (EuclideanSpace.basisFun (Fin n) ℝ i) =
        u (e x) * D.laplacian v (e x) * g.pullbackVolumeDensity e x := by
    rw [show U x = u (e x) from chartPullback_apply e u hx,
      ← D.density_mul_laplacian_eq_coordinate_divergence e he hei hx (hv (e x))]
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
theorem integral_mul_laplacian_of_tsupport_subset_chart_C1
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
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
      (hu.continuous.mul (D.continuous_laplacian hv)).continuousOn,
    g.integral_target_eq_integral_pullback_density e he hei
      (continuous_inner_gradient_C1 D hu (hv.of_le (by simp))).continuousOn]
  exact integral_mul_laplacian_chart_density_C1 D e he hei hu hv hc hs

theorem integrable_mul_laplacian_C1 (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v) (hc : HasCompactSupport u) :
    Integrable (fun x => u x * D.laplacian v x) g.volumeMeasure :=
  (hu.continuous.mul (D.continuous_laplacian hv)).integrable_of_hasCompactSupport hc.mul_right

theorem integrable_inner_gradient_C1 (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 v) (hc : HasCompactSupport u) :
    Integrable (fun x => g.inner x (D.gradient u x) (D.gradient v x)) g.volumeMeasure :=
  (continuous_inner_gradient_C1 D hu hv).integrable_of_hasCompactSupport
    (D.hasCompactSupport_inner_gradient hc v)
theorem integral_mul_laplacian_of_compact_C1_test (D : LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h) (hfc : HasCompactSupport f) :
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
  have hlocal (i : s) := integral_mul_laplacian_of_tsupport_subset_chart_C1 D
    (chartAt (EuclideanSpace ℝ (Fin n)) i.val.val).symm
    contMDiffOn_chart_symm contMDiffOn_chart (hw i) hh (hwc i) (hws i)
  calc
    _ = ∫ x, ∑ i : s, w i x * D.laplacian h x ∂g.volumeMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← Finset.sum_mul, hsum]
    _ = ∑ i : s, ∫ x, w i x * D.laplacian h x ∂g.volumeMeasure :=
      integral_finsetSum _ (fun i _ => integrable_mul_laplacian_C1 D (hw i) hh (hwc i))
    _ = -(∑ i : s, ∫ x, g.inner x (D.gradient (w i) x) (D.gradient h x)
        ∂g.volumeMeasure) := by simp only [hlocal, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i : s, g.inner x (D.gradient (w i) x) (D.gradient h x)
        ∂g.volumeMeasure) := by
      rw [integral_finsetSum _ (fun i _ => integrable_inner_gradient_C1 D (hw i) (hh.of_le (by simp)) (hwc i))]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [hgrad, map_sum, sum_apply]


#print axioms contMDiffAt_gradient_C0
#print axioms continuous_inner_gradient_C1
#print axioms integral_mul_laplacian_of_compact_C1_test
end Yamabe3.Analysis.NativeC1Green
