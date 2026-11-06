import Yamabe3.Analysis.Cylinder.NativeAngularTruncation
import Yamabe3.Analysis.Cylinder.NativeCylinderWeakTransfer

/-!
# Genuine smooth physical equations of finite angular truncations

The same radial potential multiplies every native angular mode. Actual
native Laplacian additivity therefore makes the proved scalar coefficient
equations commute with every finite angular projection. No regularity of
the infinite L2 representative is assumed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum YamabeVariation
open Yamabe3.Analysis.Delaunay

/-- A finite sum of actual lifted smooth angular modes. -/
def finitePhysical (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ) (x : E) : ℝ :=
  ∑ i ∈ s, cylinderLift (separableCylinder (q i) (angularRepresentative i)) x

theorem finitePhysical_eq_lift (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ) :
    finitePhysical s q = cylinderLift (finiteAngular s q) := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp only [finitePhysical, cylinderLift_zero, Finset.sum_const_zero]
  · let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
    have hr : 0 < ‖(y : E)‖ := norm_pos_iff.mpr hx
    change finitePhysical s q (y : E) = cylinderLift (finiteAngular s q) (y : E)
    rw [← norm_smul_sphereDirection y]
    simp only [finitePhysical, cylinderLift_smul _ hr, separableCylinder, finiteAngular,
      Finset.mul_sum]

theorem contDiffAt_finitePhysical (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiff ℝ ∞ (q i)) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (finitePhysical s q) x := by
  rw [finitePhysical_eq_lift]
  exact contDiffAt_cylinderLift (smooth_finiteAngular s q hq) hx

theorem euclidean_laplacian_finset_at {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    {x : E} (hf : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) :
    euclideanD.laplacian (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, euclideanD.laplacian (f i) x := by
  classical
  have hz : euclideanD.laplacian (fun _ : E => (0 : ℝ)) x = 0 := by
    simpa only [zero_mul] using euclideanD.laplacian_const_mul 0 (fun _ : E => (1 : ℝ)) x
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, hz]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [native_laplacian_add_at euclideanD (hf i (Finset.mem_insert_self _ _)).contMDiffAt
      (ContDiffAt.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))).contMDiffAt,
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

theorem physicalJacobi_finset_at (v : ℝ → ℝ) {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    {x : E} (hf : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) :
    physicalJacobi v (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, physicalJacobi v (f i) x := by
  unfold physicalJacobi
  rw [euclidean_laplacian_finset_at s f hf]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem physicalJacobi_finitePhysical (v : ℝ → ℝ)
    (s : Finset AngularIndex) (q f : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiff ℝ ∞ (q i))
    (heq : ∀ i ∈ s, ∀ t, modelJacobi v (angularEigenvalue i) (q i) t = f i t)
    {r : ℝ} (hr : 0 < r) (θ : S) :
    physicalJacobi v (finitePhysical s q) (r • (θ : E)) =
      physicalForcing (finiteAngular s f) (r • (θ : E)) := by
  have hn : ‖r • (θ : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  have hx : r • (θ : E) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact hr.ne' hn.symm
  have hs (i : AngularIndex) (hi : i ∈ s) :=
    smooth_separableCylinder (hq i hi) (smooth_angularRepresentative i)
  have hb : cylinderLift (radialCylinder v) (r • (θ : E)) = radialProfile v 0 r := by
    rw [cylinderLift_smul _ hr]
    simp only [radialCylinder, radialProfile, zero_sub]
  unfold finitePhysical
  rw [physicalJacobi_finset_at v s _ (fun i hi => contDiffAt_cylinderLift (hs i hi) hx)]
  calc
    _ = ∑ i ∈ s, (-8 * radialScale r / r ^ 2) * f i (-Real.log r) * angularRepresentative i θ := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := native_yamabe_linearized_eigenmode v (hq i hi)
        (smooth_angularRepresentative i) (angularRepresentative_equation i) hr θ
      rw [heq i hi] at h
      simpa only [physicalJacobi, hb] using h
    _ = _ := by
      rw [physicalForcing, cylinderLift_smul _ hr, hn]
      simp only [finiteAngular, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem physicalJacobi_finitePhysical_punctured (v : ℝ → ℝ)
    (s : Finset AngularIndex) (q f : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiff ℝ ∞ (q i))
    (heq : ∀ i ∈ s, ∀ t, modelJacobi v (angularEigenvalue i) (q i) t = f i t)
    {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (finitePhysical s q) x ∧
      physicalJacobi v (finitePhysical s q) x = physicalForcing (finiteAngular s f) x := by
  let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
  refine ⟨contDiffAt_finitePhysical s q hq hx, ?_⟩
  have h := physicalJacobi_finitePhysical v s q f hq heq (norm_pos_iff.mpr hx) (sphereDirection y)
  rw [norm_smul_sphereDirection y] at h
  exact h

#print axioms finitePhysical_eq_lift
#print axioms physicalJacobi_finitePhysical_punctured

end Yamabe3.Analysis.SpherePolar
