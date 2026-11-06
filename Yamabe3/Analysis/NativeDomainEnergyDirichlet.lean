import Yamabe3.Analysis.NativeDomainJacobianInverse

/-!
# Actual native Dirichlet solutions from general global H1 data

For arbitrary data in the genuine global native energy completion, the
negative cross-Jacobian form is a legitimate continuous functional on the
actual H1-zero domain space. Applying the already constructed domain dual
inverse gives a correction, hence the unique homogeneous solution in the
actual affine class ell + H1-zero(Omega). The same native L2 representative
satisfies all genuine compact smooth domain tests and equals ell AE outside.

This removes the earlier requirement that ell be a smooth EnergyTest. It
does not infer boundary H2, a strong normal trace, or a conormal functional
from the global form. In particular, global B(W,z) also sees the exterior
extension and is not asserted to be the boundary flux of Omega.
Actual Lean compilation pending.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace Topology

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def energyDirichletH1NormedSpace (g : RiemannianMetric 3 M) (Ω : Set M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData Ω) := inferInstance
attribute [local instance] energyDirichletH1NormedSpace

def nativeEnergyDirichletForcing (g : RiemannianMetric 3 M) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u) :
    H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData Ω →L[ℝ] ℝ :=
  -(closedYamabeJacobianForm g u hu).bilinearComp
    (ContinuousLinearMap.id ℝ (H1Zero g.leviCivitaData univ)) (nativeDomainEnergyInclusion g Ω)

@[simp] theorem nativeEnergyDirichletForcing_apply (g : RiemannianMetric 3 M) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (ell : H1Zero g.leviCivitaData univ) (z : H1Zero g.leviCivitaData Ω) :
    nativeEnergyDirichletForcing g Ω u hu ell z =
      -closedYamabeJacobianForm g u hu ell (nativeDomainEnergyInclusion g Ω z) := rfl

theorem nativeEnergyDirichletForcing_norm_le (g : RiemannianMetric 3 M) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (ell : H1Zero g.leviCivitaData univ) :
    ‖nativeEnergyDirichletForcing g Ω u hu ell‖ ≤ ‖closedYamabeJacobianForm g u hu‖ * ‖ell‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg (closedYamabeJacobianForm g u hu))
      (norm_nonneg ell))
  intro z
  rw [nativeEnergyDirichletForcing_apply, norm_neg]
  simpa only [norm_nativeDomainEnergyInclusion] using
    (closedYamabeJacobianForm g u hu).le_opNorm₂ ell (nativeDomainEnergyInclusion g Ω z)

def nativeEnergyDirichletCorrection (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) :
    H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData Ω :=
  (domainYamabeJacobianInverse g hY Ω u hu hsmall).comp (nativeEnergyDirichletForcing g Ω u hu)

def nativeEnergyDirichletSolution (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) :
    H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ :=
  ContinuousLinearMap.id ℝ _ + (nativeDomainEnergyInclusion g Ω).comp
    (nativeEnergyDirichletCorrection g hY Ω u hu hsmall)

@[simp] theorem nativeEnergyDirichletSolution_apply (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) (ell : H1Zero g.leviCivitaData univ) :
    nativeEnergyDirichletSolution g hY Ω u hu hsmall ell = ell + nativeDomainEnergyInclusion g Ω
      (nativeEnergyDirichletCorrection g hY Ω u hu hsmall ell) := rfl

theorem nativeEnergyDirichletSolution_homogeneous (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) (ell : H1Zero g.leviCivitaData univ)
    (z : H1Zero g.leviCivitaData Ω) :
    closedYamabeJacobianForm g u hu (nativeEnergyDirichletSolution g hY Ω u hu hsmall ell)
      (nativeDomainEnergyInclusion g Ω z) = 0 := by
  have h := domainYamabeJacobianInverse_spec g hY Ω u hu hsmall
    (nativeEnergyDirichletForcing g Ω u hu ell) z
  change closedYamabeJacobianForm g u hu (nativeDomainEnergyInclusion g Ω
    (nativeEnergyDirichletCorrection g hY Ω u hu hsmall ell))
      (nativeDomainEnergyInclusion g Ω z) =
        -closedYamabeJacobianForm g u hu ell (nativeDomainEnergyInclusion g Ω z) at h
  rw [nativeEnergyDirichletSolution_apply, map_add, ContinuousLinearMap.add_apply, h, add_neg_cancel]

/-- All actual compact smooth domain tests use the original native volume
and original native Jacobian. No smoothness of ell or W is assumed. -/
theorem nativeEnergyDirichletSolution_native_test (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) (ell : H1Zero g.leviCivitaData univ)
    (φ : EnergyTest g.leviCivitaData Ω) :
    (∫ x, (-8 * g.leviCivitaData.laplacian φ x + g.leviCivitaData.scalarCurvature x * φ x -
      30 * u x ^ 4 * φ x) * toL2 g.leviCivitaData univ
        (nativeEnergyDirichletSolution g hY Ω u hu hsmall ell) x ∂g.volumeMeasure) = 0 := by
  have h := nativeEnergyDirichletSolution_homogeneous g hY Ω u hu hsmall ell
    (φ : H1Zero g.leviCivitaData Ω)
  rw [nativeDomainEnergyInclusion_coe, closedYamabeJacobianForm_test_eq_integral] at h
  exact h

theorem nativeEnergyDirichletSolution_ae_outside (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M) (hΩ : MeasurableSet Ω)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) (ell : H1Zero g.leviCivitaData univ) :
    ∀ᵐ x ∂g.volumeMeasure, x ∉ Ω →
      toL2 g.leviCivitaData univ (nativeEnergyDirichletSolution g hY Ω u hu hsmall ell) x =
        toL2 g.leviCivitaData univ ell x := by
  let w := nativeEnergyDirichletCorrection g hY Ω u hu hsmall ell
  have he : toL2 g.leviCivitaData univ (nativeEnergyDirichletSolution g hY Ω u hu hsmall ell) =
      toL2 g.leviCivitaData univ ell + toL2 g.leviCivitaData Ω w := by
    rw [nativeEnergyDirichletSolution_apply, map_add, nativeDomainEnergyInclusion_toL2]
  rw [he]
  filter_upwards [Lp.coeFn_add (toL2 g.leviCivitaData univ ell) (toL2 g.leviCivitaData Ω w),
    toL2_ae_zero_outside hΩ w] with x hadd hz
  intro hx
  rw [hadd]
  simp only [Pi.add_apply, hz hx, add_zero]

theorem nativeEnergyDirichletCorrection_unique (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) (ell : H1Zero g.leviCivitaData univ)
    (w : H1Zero g.leviCivitaData Ω)
    (hw : ∀ z : H1Zero g.leviCivitaData Ω,
      closedYamabeJacobianForm g u hu (ell + nativeDomainEnergyInclusion g Ω w)
        (nativeDomainEnergyInclusion g Ω z) = 0) :
    w = nativeEnergyDirichletCorrection g hY Ω u hu hsmall ell := by
  apply domainYamabeJacobianInverse_unique g hY Ω u hu hsmall
    (nativeEnergyDirichletForcing g Ω u hu ell) w
  intro z
  rw [domainYamabeJacobianForm_apply, nativeEnergyDirichletForcing_apply]
  have h := hw z
  simp only [map_add, ContinuousLinearMap.add_apply] at h
  linarith only [h]

/-- The inverse factor is uniform before domain and background. The norm
of the actual background Jacobian form remains explicit, so this result
does not claim a new uniform upper bound on that form. -/
theorem exists_uniform_nativeEnergyDirichlet_bound (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set M) (u : M → ℝ)
      (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
      (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
        Target.yamabeConstant g),
      ‖nativeEnergyDirichletCorrection g hY Ω u hu hsmall‖ ≤ C * ‖closedYamabeJacobianForm g u hu‖ ∧
      ‖nativeEnergyDirichletSolution g hY Ω u hu hsmall‖ ≤ 1 + C * ‖closedYamabeJacobianForm g u hu‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_domainYamabeJacobianInverse_bound g hY
  refine ⟨C, hC, fun Ω u hu hsmall => ?_⟩
  have hR := (hbound Ω u hu hsmall).1
  have hc (ell : H1Zero g.leviCivitaData univ) :
      ‖nativeEnergyDirichletCorrection g hY Ω u hu hsmall ell‖ ≤
        (C * ‖closedYamabeJacobianForm g u hu‖) * ‖ell‖ := by
    have h1 := (domainYamabeJacobianInverse g hY Ω u hu hsmall).le_opNorm
      (nativeEnergyDirichletForcing g Ω u hu ell)
    have h2 := mul_le_mul_of_nonneg_right hR (norm_nonneg
      (nativeEnergyDirichletForcing g Ω u hu ell))
    have h3 := mul_le_mul_of_nonneg_left (nativeEnergyDirichletForcing_norm_le g Ω u hu ell) hC.le
    exact h1.trans (h2.trans (by simpa only [mul_assoc] using h3))
  refine ⟨ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hC.le (ContinuousLinearMap.opNorm_nonneg (closedYamabeJacobianForm g u hu)))
    hc, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ell
  rw [nativeEnergyDirichletSolution_apply]
  calc
    _ ≤ ‖ell‖ + ‖nativeDomainEnergyInclusion g Ω
        (nativeEnergyDirichletCorrection g hY Ω u hu hsmall ell)‖ := norm_add_le _ _
    _ ≤ ‖ell‖ + (C * ‖closedYamabeJacobianForm g u hu‖) * ‖ell‖ := by
      rw [norm_nativeDomainEnergyInclusion]
      exact add_le_add le_rfl (hc ell)
    _ = _ := by ring

#print axioms nativeEnergyDirichletSolution_homogeneous
#print axioms nativeEnergyDirichletSolution_native_test
#print axioms nativeEnergyDirichletSolution_ae_outside
#print axioms nativeEnergyDirichletCorrection_unique
#print axioms exists_uniform_nativeEnergyDirichlet_bound

end Yamabe3.Analysis
