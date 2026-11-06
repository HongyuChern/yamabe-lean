import Yamabe3.W6.EuclideanCylinder
import Yamabe3.W6.RoundGeometry
import Yamabe3.W6.TwoPointPDE
import Yamabe3.Geometry.PuncturedConnected
import Yamabe3.Geometry.SphericalPuncturedTransport

/-!
# Complete solutions at any two prescribed round-sphere points

This file closes the two-point control case through the actual constructed
function and native metric. Its theorem has cardinality exactly two, and
is not an existence theorem for arbitrary finite sets of larger cardinality.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace PoincareMT
open scoped Manifold ContDiff Bundle

namespace Yamabe3.W6

open Yamabe3.Geometry

theorem euclideanCylinderFunction_complete :
    MetricComplete (MetricSurgery.positiveScaling
      (restrictMetric (RiemannianMetric.euclideanMetric 3) euclideanPuncturedOpen)
      (fun x => euclideanCylinderFunction x ^ 4)
      (euclideanCylinderFunction_smooth.pow 4)
      (fun x => pow_pos (euclideanCylinderFunction_pos x) 4)) := by
  apply euclidean_cylindrical_complete euclideanCylinderFunction
    euclideanCylinderFunction_smooth euclideanCylinderFunction_pos
    (cylinderAmplitude ^ 2) (pow_pos cylinderAmplitude_pos 2)
  intro x
  exact (euclideanCylinderFunction_sq x).ge

theorem twoPointYamabeFunction_complete (p q : Sphere) (hpq : p ≠ q) :
    MetricComplete (MetricSurgery.positiveScaling
      (restrictMetric roundMetric (twoPointOpen p q))
      (fun x => twoPointYamabeFunction p q hpq x ^ 4)
      ((twoPointYamabeFunction_smooth p q hpq).pow 4)
      (fun x => pow_pos (twoPointYamabeFunction_pos p q hpq x) 4)) := by
  exact (conformal_diffeomorph_final_complete_iff
    (restrictMetric roundMetric (twoPointOpen p q))
    (restrictMetric (RiemannianMetric.euclideanMetric 3) euclideanPuncturedOpen)
    (twoPointDiffeomorph p q hpq) (twoPointConformalFactor p q)
    euclideanCylinderFunction (twoPointConformalFactor_smooth p q)
    euclideanCylinderFunction_smooth (twoPointConformalFactor_pos p q)
    euclideanCylinderFunction_pos (twoPoint_forward_metric p q hpq)).mp
      euclideanCylinderFunction_complete

theorem twoPointYamabeFunction_normalized_equation
    (p q : Sphere) (hpq : p ≠ q) (x : twoPointOpen p q) :
    -8 * (restrictMetric roundMetric (twoPointOpen p q)).leviCivitaData.laplacian
      (twoPointYamabeFunction p q hpq) x + 6 * twoPointYamabeFunction p q hpq x =
        6 * twoPointYamabeFunction p q hpq x ^ 5 := by
  have h := twoPointYamabeFunction_native_equation p q hpq x
  have hs := punctured_round_scalarCurvature_eq_six ({p, q} : Finset Sphere) x
  change (restrictMetric roundMetric (twoPointOpen p q)).leviCivitaData.scalarCurvature x = 6 at hs
  simpa only [hs] using h

/-- Complete native two-point existence, including finite intrinsic
distances and every smooth geodesic initial condition. -/
theorem round_two_point_conclusion (p q : Sphere) (hpq : p ≠ q) :
    Target.puncturedConclusion roundMetric ({p, q} : Finset Sphere) := by
  let g := restrictMetric roundMetric (twoPointOpen p q)
  let u := twoPointYamabeFunction p q hpq
  have hu := twoPointYamabeFunction_smooth p q hpq
  have hp := twoPointYamabeFunction_pos p q hpq
  have hc := twoPointYamabeFunction_complete p q hpq
  refine ⟨u, hu, hp, twoPointYamabeFunction_native_equation p q hpq, hc, ?_, ?_⟩
  · intro x y htop
    let flat := restrictMetric (RiemannianMetric.euclideanMetric 3) euclideanPuncturedOpen
    let F := twoPointDiffeomorph p q hpq
    have hdist := conformal_diffeomorph_final_edist g flat F (twoPointConformalFactor p q)
      euclideanCylinderFunction (twoPointConformalFactor_smooth p q)
      euclideanCylinderFunction_smooth (twoPointConformalFactor_pos p q)
      euclideanCylinderFunction_pos (twoPoint_forward_metric p q hpq) x y
    exact edist_ne_top_of_finset_complement
      ({0} : Finset (EuclideanSpace ℝ (Fin 3))) euclideanPuncturedOpen rfl _
      (F x) (F y) (hdist.trans htop)
  · intro x v
    obtain ⟨γ, hγ, hγ0, hv⟩ := RiemannianMetric.exists_global_geodesic _ hc x v
    exact ⟨γ, RiemannianMetric.contMDiff_global_geodesic hγ, hγ, hγ0, hv⟩

/-- The finset interface retains both arbitrary prescribed points. -/
theorem round_card_two_conclusion (Λ : Finset Sphere) (hΛ : Λ.card = 2) :
    Target.puncturedConclusion roundMetric Λ := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hΛ
  exact round_two_point_conclusion p q hpq

section Transport

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- Actual conformal equivalence data transport the proved two-point
theorem to the original metric and the exact original two-point set. -/
theorem conformal_round_card_two_conclusion
    (g : RiemannianMetric 3 M)
    (F : Diffeomorph (𝓡 3) (𝓡 3) M Sphere ∞)
    (θ : M → ℝ) (hθ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ θ)
    (hθpos : ∀ x, 0 < θ x)
    (hF : ∀ x v w, roundMetric.inner (F x)
      (mfderiv (𝓡 3) (𝓡 3) F x v) (mfderiv (𝓡 3) (𝓡 3) F x w) =
        θ x ^ 4 * g.inner x v w)
    (Λ : Finset M) (hΛ : Λ.card = 2) :
    Target.puncturedConclusion g Λ := by
  apply puncturedConclusion_conformal_transport g roundMetric F Λ θ hθ hθpos hF
  apply round_card_two_conclusion
  simpa only [Finset.card_map] using hΛ

end Transport

#print axioms euclideanCylinderFunction_complete
#print axioms twoPointYamabeFunction_complete
#print axioms twoPointYamabeFunction_normalized_equation
#print axioms round_two_point_conclusion
#print axioms round_card_two_conclusion
#print axioms conformal_round_card_two_conclusion

end Yamabe3.W6
