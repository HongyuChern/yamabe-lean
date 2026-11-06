import Yamabe3.Analysis.Cylinder.NativeAngularLinearization
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Order.Filter.Finite

/-!
# Actual smooth native angular finite sums

Every representative below is chosen from the proved native eigenfunction
existence theorem. The finite smooth scalar sum is identified almost
everywhere with the actual finite sum in the native Hilbert space.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum
open Poincare.Geometry.Riemannian.SpaceForm

def angularRepresentative (i : AngularIndex) : S → ℝ :=
  Classical.choose (exists_smooth_angular_eigenfunction i)

theorem smooth_angularRepresentative (i : AngularIndex) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (angularRepresentative i) :=
  (Classical.choose_spec (exists_smooth_angular_eigenfunction i)).1

theorem angularRepresentative_ae (i : AngularIndex) :
    angularRepresentative i =ᵐ[(roundSphereMetric 2).volumeMeasure] (angularBasis i : S → ℝ) :=
  (Classical.choose_spec (exists_smooth_angular_eigenfunction i)).2.1

theorem angularRepresentative_equation (i : AngularIndex) (x : S) :
    -sphereD.laplacian (angularRepresentative i) x = angularEigenvalue i * angularRepresentative i x :=
  (Classical.choose_spec (exists_smooth_angular_eigenfunction i)).2.2.2 x

def finiteAngular (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ) (p : ℝ × S) : ℝ :=
  ∑ i ∈ s, q i p.1 * angularRepresentative i p.2

theorem smooth_finiteAngular (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiff ℝ ∞ (q i)) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (finiteAngular s q) := by
  apply contMDiff_finsetSum
  intro i hi
  exact smooth_separableCylinder (hq i hi) (smooth_angularRepresentative i)

theorem finiteAngular_ae (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ) (t : ℝ) :
    (fun x : S => finiteAngular s q (t, x)) =ᵐ[(roundSphereMetric 2).volumeMeasure]
      (∑ i ∈ s, q i t • angularBasis i : AngularL2) := by
  have hm (i : AngularIndex) :
      (fun x : S => q i t * angularRepresentative i x) =ᵐ[(roundSphereMetric 2).volumeMeasure]
        (q i t • angularBasis i : AngularL2) := by
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul (q i t) (angularBasis i))
    filter_upwards [angularRepresentative_ae i, hc] with x hx hc
    rw [hx]
    simpa only [Pi.smul_apply, smul_eq_mul] using (hc (mem_univ x)).symm
  have hall : ∀ᵐ x ∂(roundSphereMetric 2).volumeMeasure,
      ∀ i ∈ s, q i t * angularRepresentative i x = (q i t • angularBasis i : AngularL2) x :=
    (Filter.eventually_all_finset s).mpr (fun i _ => hm i)
  have hsum := (ae_restrict_iff' MeasurableSet.univ).mp
    (Lp.coeFn_fun_finsetSum s (fun i => q i t • angularBasis i))
  filter_upwards [hall, hsum] with x hx hsum
  rw [hsum (mem_univ x)]
  exact Finset.sum_congr rfl (fun i hi => hx i hi)

theorem integral_finiteAngular_square (s : Finset AngularIndex)
    (q : AngularIndex → ℝ → ℝ) (t : ℝ) :
    (∫ x : S, finiteAngular s q (t, x) ^ 2 ∂(roundSphereMetric 2).volumeMeasure) =
      ‖∑ i ∈ s, q i t • angularBasis i‖ ^ 2 := by
  let U : AngularL2 := ∑ i ∈ s, q i t • angularBasis i
  calc
    _ = ∫ x : S, U x ^ 2 ∂(roundSphereMetric 2).volumeMeasure := by
      apply integral_congr_ae
      filter_upwards [finiteAngular_ae s q t] with x hx
      exact congrArg (fun z : ℝ => z ^ 2) hx
    _ = inner ℝ U U := by
      simp only [L2.inner_def, setIntegral_univ, RCLike.inner_apply, conj_trivial, sq]
    _ = _ := real_inner_self_eq_norm_sq U

#print axioms smooth_finiteAngular
#print axioms finiteAngular_ae
#print axioms integral_finiteAngular_square

end Yamabe3.Analysis.SpherePolar
