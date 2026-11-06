import Yamabe3.W6.RoundGeometryMinimal

/-!
# Public W6 interface for the actual unit round metric

The independently compiled native proof is in `RoundGeometryMinimal`.
These public names preserve the canonical W6 interface and the literal metric,
sectional curvature, scalar curvature, open restriction and Laplacian meanings.
-/

noncomputable section
set_option autoImplicit false
open PoincareMT
open scoped Manifold ContDiff Bundle

namespace Yamabe3.W6

abbrev roundMetric : RiemannianMetric 3 Sphere := MinimalRoundGeometry.roundMetric

theorem round_sectionalCurvature_eq_one
    (D : LeviCivitaData roundMetric) (x : Sphere)
    (u v : TangentSpace (𝓡 3) x)
    (hu : roundMetric.inner x u u = 1)
    (hv : roundMetric.inner x v v = 1)
    (huv : roundMetric.inner x u v = 0) :
    D.sectionalCurvature x u v = 1 :=
  MinimalRoundGeometry.round_sectionalCurvature_eq_one D x u v hu hv huv

theorem round_scalarCurvature_eq_six
    (D : LeviCivitaData roundMetric) (x : Sphere) :
    D.scalarCurvature x = 6 :=
  MinimalRoundGeometry.round_scalarCurvature_eq_six D x

theorem punctured_round_scalarCurvature_eq_six
    (Λ : Finset Sphere) (x : Target.puncturedOpen Λ) :
    (Geometry.restrictMetric roundMetric (Target.puncturedOpen Λ)).leviCivitaData.scalarCurvature x = 6 :=
  MinimalRoundGeometry.punctured_round_scalarCurvature_eq_six Λ x

theorem punctured_round_equation_iff
    (Λ : Finset Sphere) (u : Target.puncturedOpen Λ → ℝ)
    (x : Target.puncturedOpen Λ) :
    let D := (Geometry.restrictMetric roundMetric (Target.puncturedOpen Λ)).leviCivitaData
    (-8 * D.laplacian u x + D.scalarCurvature x * u x = 6 * u x ^ 5) ↔
      (-8 * D.laplacian u x + 6 * u x = 6 * u x ^ 5) :=
  MinimalRoundGeometry.punctured_round_equation_iff Λ u x

#print axioms round_sectionalCurvature_eq_one
#print axioms round_scalarCurvature_eq_six
#print axioms punctured_round_scalarCurvature_eq_six
#print axioms punctured_round_equation_iff

end Yamabe3.W6
