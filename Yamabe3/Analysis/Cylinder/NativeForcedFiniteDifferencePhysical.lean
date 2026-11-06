import Yamabe3.Analysis.NativeForcedHalfEndFiniteDifference
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndFiniteWeakEquation

/-!
# Pointwise identity of the actual finite physical difference

The literal two indicator coefficients are summed over the actual union
of the two finite spectral sets. Finite-sum algebra proves equality of
the original angular functions at every point, before any physical lift
or derivative is taken. The existing pointwise linearity of the lift
then identifies the original two physical fields.

Their already produced finite C2 regularity gives the actual Frechet
derivative of this same difference on the punctured unit ball. No
almost-everywhere representative identity is used in these equalities.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Manifold ContDiff Topology RealInnerProductSpace BoundedContinuousFunction

attribute [local instance] Classical.propDecidable

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

private theorem sum_indicator_on_superset {ι : Type*} [DecidableEq ι]
    (s u : Finset ι) (hsu : s ⊆ u) (a : ι → ℝ) :
    (∑ i ∈ u, if i ∈ s then a i else 0) = ∑ i ∈ s, a i := by
  calc
    _ = ∑ i ∈ s, if i ∈ s then a i else 0 :=
      (Finset.sum_subset hsu (fun i _ hi => if_neg hi)).symm
    _ = _ := Finset.sum_congr rfl (fun i hi => if_pos hi)

/-- The empty finite projection has exactly the zero physical lift. -/
theorem cylinderLift_projectedAngular_empty (U : ℝ → AngularL2) :
    cylinderLift (projectedAngular ∅ U) = 0 := by
  rw [projectedAngular, ← finitePhysical_eq_lift]
  funext x
  simp only [finitePhysical, Finset.sum_empty, Pi.zero_apply]

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The actual indicator coefficients reconstruct the difference of the
same chosen smooth finite angular functions at every point. -/
theorem native_forced_finiteDifference_angular_eq
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) :
    finiteAngular (s ∪ t)
      (nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t) =
      (fun p =>
        projectedAngular s (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F) p -
        projectedAngular t (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F) p) := by
  classical
  funext p
  simp only [finiteAngular, nativeHalfHighDirichletFiniteDifferenceCoefficient_apply,
    sub_mul, Finset.sum_sub_distrib, projectedAngular]
  congr 1
  · simpa only [ite_mul, zero_mul] using
      sum_indicator_on_superset s (s ∪ t) Finset.subset_union_left
        (fun i => inner ℝ (angularBasis i)
          (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F p.1) * angularRepresentative i p.2)
  · simpa only [ite_mul, zero_mul] using
      sum_indicator_on_superset t (s ∪ t) Finset.subset_union_right
        (fun i => inner ℝ (angularBasis i)
          (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F p.1) * angularRepresentative i p.2)

/-- Equality of the actual physical functions, including the retained
value at zero. It is proved pointwise, not merely in a quotient space. -/
theorem native_forced_finiteDifference_physical_eq
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) :
    finitePhysical (s ∪ t)
      (nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t) =
      (fun x =>
        cylinderLift (projectedAngular s
          (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)) x -
        cylinderLift (projectedAngular t
          (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)) x) := by
  rw [finitePhysical_eq_lift,
    native_forced_finiteDifference_angular_eq hκ0 hκ1 V hV hV0 F s t,
    cylinderLift_sub]

/-- The actual Frechet derivative of that original difference is the
difference of the two actual Frechet derivatives inside the physical
domain, using their produced finite C2 regularity. -/
theorem native_forced_finiteDifference_fderiv_eq
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex)
    {x : E} (hx : x ∈ Metric.ball (0 : E) 1 \ {(0 : E)}) :
    fderiv ℝ (finitePhysical (s ∪ t)
      (nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t)) x =
      fderiv ℝ (cylinderLift (projectedAngular s
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))) x -
      fderiv ℝ (cylinderLift (projectedAngular t
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))) x := by
  have hO : IsOpen (Metric.ball (0 : E) 1 \ {(0 : E)}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  have hs := (native_forced_halfEnd_finite_lift_contDiffOn_two
    hκ0 hκ1 V hV hV0 F s).contDiffAt (hO.mem_nhds hx)
  have ht := (native_forced_halfEnd_finite_lift_contDiffOn_two
    hκ0 hκ1 V hV hV0 F t).contDiffAt (hO.mem_nhds hx)
  rw [native_forced_finiteDifference_physical_eq hκ0 hκ1 V hV hV0 F s t]
  exact fderiv_fun_sub (hs.differentiableAt (by norm_num)) (ht.differentiableAt (by norm_num))

/-- Coordinate evaluation of the same actual derivative equality. -/
theorem native_forced_finiteDifference_partial_eq
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex)
    {x : E} (hx : x ∈ Metric.ball (0 : E) 1 \ {(0 : E)}) (j : Fin 3) :
    fderiv ℝ (finitePhysical (s ∪ t)
      (nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t)) x
        (EuclideanSpace.single j 1) =
      fderiv ℝ (cylinderLift (projectedAngular s
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))) x (EuclideanSpace.single j 1) -
      fderiv ℝ (cylinderLift (projectedAngular t
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))) x (EuclideanSpace.single j 1) := by
  simpa only [ContinuousLinearMap.sub_apply] using
    congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single j 1))
      (native_forced_finiteDifference_fderiv_eq hκ0 hκ1 V hV hV0 F s t hx)

#print axioms cylinderLift_projectedAngular_empty
#print axioms native_forced_finiteDifference_angular_eq
#print axioms native_forced_finiteDifference_physical_eq
#print axioms native_forced_finiteDifference_fderiv_eq
#print axioms native_forced_finiteDifference_partial_eq

end Yamabe3.Analysis.SpherePolar
