import Yamabe3.Geometry.ConformalYamabe
import PoincareLib.Geometry.Riemannian.Connection.Construction
import PoincareLib.Geometry.Riemannian.Connection.Uniqueness
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareLib.Geometry.Riemannian.Homothety.Completeness
import PoincareLib.Geometry.Riemannian.Geodesic.Complete

/-!
# Exact conformal transport in dimension three

The scaling factors below multiply the actual native metrics.  All identities
use the differential of the supplied diffeomorphism.  No existence assertion
for a singular Yamabe solution is assumed or manufactured in this module.

The statements apply to any smooth three-manifold, in particular to the open
punctured manifolds obtained after restricting a conformal equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Bundle ENNReal

noncomputable section

namespace Yamabe3.Geometry

open PoincareMT PoincareMT.MetricSurgery

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem native_metric_eq_of_inner (g h : RiemannianMetric n M)
    (he : ∀ x v w, g.inner x v w = h.inner x v w) : g = h := by
  have hi : g.inner = h.inner := by
    funext x
    ext v w
    exact he x v w
  cases g
  cases h
  cases hi
  rfl

/-- Multiplication of the positive functions is exactly composition of native
fourth-power metric scalings, rather than an isometry to another metric. -/
theorem positiveScaling_pow_four_mul
    (g : RiemannianMetric n M) (θ u : M → ℝ)
    (hθ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ θ)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hθpos : ∀ x, 0 < θ x) (hupos : ∀ x, 0 < u x) :
    positiveScaling (positiveScaling g (fun x => θ x ^ 4) (hθ.pow 4)
      (fun x => pow_pos (hθpos x) 4))
      (fun x => u x ^ 4) (hu.pow 4) (fun x => pow_pos (hupos x) 4) =
    positiveScaling g (fun x => (θ x * u x) ^ 4) ((hθ.mul hu).pow 4)
      (fun x => pow_pos (mul_pos (hθpos x) (hupos x)) 4) := by
  apply native_metric_eq_of_inner
  intro x v w
  simp only [positiveScaling_inner]
  ring

end Yamabe3.Geometry

namespace Yamabe3.Geometry

open PoincareMT PoincareMT.MetricSurgery

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- A change of conformal representative sends `u` to `θ u`.  The two PDEs
refer to the canonical native Levi-Civita connections of the two backgrounds.
The proof compares scalar curvature of the same final metric. -/
theorem yamabe_equation_change_representative_iff
    (g : RiemannianMetric 3 M) (θ u : M → ℝ)
    (hθ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ θ)
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hθpos : ∀ x, 0 < θ x) (hupos : ∀ x, 0 < u x) (x : M) :
    let h := positiveScaling g (fun y => θ y ^ 4) (hθ.pow 4)
      (fun y => pow_pos (hθpos y) 4)
    (-8 * h.leviCivitaData.laplacian u x +
      h.leviCivitaData.scalarCurvature x * u x = 6 * u x ^ 5) ↔
    (-8 * g.leviCivitaData.laplacian (fun y => θ y * u y) x +
      g.leviCivitaData.scalarCurvature x * (θ x * u x) =
        6 * (θ x * u x) ^ 5) := by
  dsimp only
  let h := positiveScaling g (fun y => θ y ^ 4) (hθ.pow 4)
    (fun y => pow_pos (hθpos y) 4)
  let k := positiveScaling h (fun y => u y ^ 4) (hu.pow 4)
    (fun y => pow_pos (hupos y) 4)
  let l := positiveScaling g (fun y => (θ y * u y) ^ 4) ((hθ.mul hu).pow 4)
    (fun y => pow_pos (mul_pos (hθpos y) (hupos y)) 4)
  have he : k = l := positiveScaling_pow_four_mul g θ u hθ hu hθpos hupos
  have hcurv : k.leviCivitaData.scalarCurvature x =
      l.leviCivitaData.scalarCurvature x := by rw [he]
  have hfirst := scalarCurvature_eq_six_iff h h.leviCivitaData hu hupos
    k.leviCivitaData x
  have hsecond := scalarCurvature_eq_six_iff g g.leviCivitaData (hθ.mul hu)
    (fun y => mul_pos (hθpos y) (hupos y)) l.leviCivitaData x
  exact hfirst.symm.trans ((congrArg (fun r : ℝ => r = 6) hcurv).to_iff.trans hsecond)

variable {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]

/-- The supplied conformal pullback identity implies an exact isometry of
the final Yamabe metrics.  Its factor is one, with no scalar renormalization. -/
theorem conformal_diffeomorph_final_metric_homothety
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (θ : M → ℝ) (u : N → ℝ)
    (hθ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ θ)
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hθpos : ∀ x, 0 < θ x) (hupos : ∀ x, 0 < u x)
    (hF : ∀ x v w, h.inner (F x) (mfderiv (𝓡 3) (𝓡 3) F x v)
        (mfderiv (𝓡 3) (𝓡 3) F x w) = θ x ^ 4 * g.inner x v w) :
    MetricHomothety
      (positiveScaling g (fun x => (θ x * u (F x)) ^ 4)
        ((hθ.mul (hu.comp F.contMDiff)).pow 4)
        (fun x => pow_pos (mul_pos (hθpos x) (hupos (F x))) 4))
      (positiveScaling h (fun y => u y ^ 4) (hu.pow 4)
        (fun y => pow_pos (hupos y) 4)) F 1 := by
  intro x v w
  simp only [positiveScaling_inner, hF, one_mul]
  ring

/-- Transport of the actual PDE through actual conformal equivalence data.
The background scalar curvatures need not be constant. -/
theorem yamabe_equation_conformal_diffeomorph_iff
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (θ : M → ℝ) (u : N → ℝ)
    (hθ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ θ)
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hθpos : ∀ x, 0 < θ x) (hupos : ∀ x, 0 < u x)
    (hF : ∀ x v w, h.inner (F x) (mfderiv (𝓡 3) (𝓡 3) F x v)
        (mfderiv (𝓡 3) (𝓡 3) F x w) = θ x ^ 4 * g.inner x v w)
    (x : M) :
    (-8 * h.leviCivitaData.laplacian u (F x) +
      h.leviCivitaData.scalarCurvature (F x) * u (F x) = 6 * u (F x) ^ 5) ↔
    (-8 * g.leviCivitaData.laplacian (fun y => θ y * u (F y)) x +
      g.leviCivitaData.scalarCurvature x * (θ x * u (F x)) =
        6 * (θ x * u (F x)) ^ 5) := by
  let k := positiveScaling g (fun y => (θ y * u (F y)) ^ 4)
    ((hθ.mul (hu.comp F.contMDiff)).pow 4)
    (fun y => pow_pos (mul_pos (hθpos y) (hupos (F y))) 4)
  let l := positiveScaling h (fun y => u y ^ 4) (hu.pow 4)
    (fun y => pow_pos (hupos y) 4)
  have hm := conformal_diffeomorph_final_metric_homothety g h F θ u
    hθ hu hθpos hupos hF
  have hc : k.leviCivitaData.scalarCurvature x =
      l.leviCivitaData.scalarCurvature (F x) := by
    apply k.leviCivitaData.scalarCurvature_eq_of_local_isometry
      l.leviCivitaData isOpen_univ F.contMDiff.contMDiffOn
    · intro y _ v w
      simpa only [one_mul] using (hm y v w).symm
    · exact Set.mem_univ x
  have hfirst := scalarCurvature_eq_six_iff h h.leviCivitaData hu hupos
    l.leviCivitaData (F x)
  have hsecond := scalarCurvature_eq_six_iff g g.leviCivitaData
    (hθ.mul (hu.comp F.contMDiff))
    (fun y => mul_pos (hθpos y) (hupos (F y))) k.leviCivitaData x
  exact hfirst.symm.trans ((congrArg (fun r : ℝ => r = 6) hc.symm).to_iff.trans hsecond)

/- The next statements use exactly the final metrics of the previous theorem. -/
theorem conformal_diffeomorph_final_edist
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (θ : M → ℝ) (u : N → ℝ)
    (hθ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ θ)
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hθpos : ∀ x, 0 < θ x) (hupos : ∀ x, 0 < u x)
    (hF : ∀ x v w, h.inner (F x) (mfderiv (𝓡 3) (𝓡 3) F x v)
        (mfderiv (𝓡 3) (𝓡 3) F x w) = θ x ^ 4 * g.inner x v w)
    (x y : M) :
    (positiveScaling h (fun z => u z ^ 4) (hu.pow 4)
      (fun z => pow_pos (hupos z) 4)).edist (F x) (F y) =
    (positiveScaling g (fun z => (θ z * u (F z)) ^ 4)
      ((hθ.mul (hu.comp F.contMDiff)).pow 4)
      (fun z => pow_pos (mul_pos (hθpos z) (hupos (F z))) 4)).edist x y := by
  simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using
    Homothety.homothety_edist _ _ F 1 (by norm_num)
      (conformal_diffeomorph_final_metric_homothety g h F θ u hθ hu hθpos hupos hF) x y

theorem conformal_diffeomorph_final_complete_iff [T3Space M] [T3Space N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (θ : M → ℝ) (u : N → ℝ)
    (hθ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ θ)
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hθpos : ∀ x, 0 < θ x) (hupos : ∀ x, 0 < u x)
    (hF : ∀ x v w, h.inner (F x) (mfderiv (𝓡 3) (𝓡 3) F x v)
        (mfderiv (𝓡 3) (𝓡 3) F x w) = θ x ^ 4 * g.inner x v w) :
    MetricComplete (positiveScaling h (fun z => u z ^ 4) (hu.pow 4)
      (fun z => pow_pos (hupos z) 4)) ↔
    MetricComplete (positiveScaling g (fun z => (θ z * u (F z)) ^ 4)
      ((hθ.mul (hu.comp F.contMDiff)).pow 4)
      (fun z => pow_pos (mul_pos (hθpos z) (hupos (F z))) 4)) := by
  exact Homothety.homothety_complete_iff _ _ F 1 (by norm_num)
    (conformal_diffeomorph_final_metric_homothety g h F θ u hθ hu hθpos hupos hF)

/-- Completeness of the transported final metric gives all initial positions
and coordinate velocities, with smooth global geodesics on the real line. -/
theorem conformal_diffeomorph_final_global_geodesic [T3Space M] [T3Space N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (θ : M → ℝ) (u : N → ℝ)
    (hθ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ θ)
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hθpos : ∀ x, 0 < θ x) (hupos : ∀ x, 0 < u x)
    (hF : ∀ x v w, h.inner (F x) (mfderiv (𝓡 3) (𝓡 3) F x v)
        (mfderiv (𝓡 3) (𝓡 3) F x w) = θ x ^ 4 * g.inner x v w)
    (hc : MetricComplete (positiveScaling h (fun z => u z ^ 4) (hu.pow 4)
      (fun z => pow_pos (hupos z) 4)))
    (x : M) (v : EuclideanSpace ℝ (Fin 3)) :
    let k := positiveScaling g (fun z => (θ z * u (F z)) ^ 4)
      ((hθ.mul (hu.comp F.contMDiff)).pow 4)
      (fun z => pow_pos (mul_pos (hθpos z) (hupos (F z))) 4)
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ ∧
      k.IsGeodesicOn γ Set.univ ∧ γ 0 = x ∧
      HasDerivAt (fun t => extChartAt (𝓡 3) x (γ t)) v 0 := by
  dsimp only
  have hc' := (conformal_diffeomorph_final_complete_iff g h F θ u
    hθ hu hθpos hupos hF).mp hc
  obtain ⟨γ, hγ, hx, hv⟩ := RiemannianMetric.exists_global_geodesic _ hc' x v
  exact ⟨γ, RiemannianMetric.contMDiff_global_geodesic hγ, hγ, hx, hv⟩

#print axioms positiveScaling_pow_four_mul
#print axioms yamabe_equation_change_representative_iff
#print axioms conformal_diffeomorph_final_metric_homothety
#print axioms yamabe_equation_conformal_diffeomorph_iff
#print axioms conformal_diffeomorph_final_edist
#print axioms conformal_diffeomorph_final_complete_iff
#print axioms conformal_diffeomorph_final_global_geodesic

end Yamabe3.Geometry
