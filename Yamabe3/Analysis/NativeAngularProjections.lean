import Yamabe3.Analysis.NativeAngularInverse

/-!
# Actual native low and high angular projections

The bounded diagonal maps act on the true native round-sphere Hilbert basis.
Their norms are at most one before any time supremum is taken. The two
projections split every actual native L2 source and preserve its smooth
spectral coefficients; no coordinate-wise sup summability is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum

/-- Projection onto any specified subset of the actual native spectrum. -/
def nativeAngularProjection (p : AngularIndex → Prop) : AngularL2 →L[ℝ] AngularL2 := by
  classical
  exact angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((spectralDiagonal (fun i => if p i then (1 : ℝ) else 0)
      (by norm_num : (0 : ℝ) ≤ 1) (fun i => by split_ifs <;> norm_num)).comp
      angularBasis.repr.toLinearIsometry.toContinuousLinearMap)

theorem nativeAngularProjection_coefficient (p : AngularIndex → Prop)
    (u : AngularL2) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeAngularProjection p u) =
      if p i then inner ℝ (angularBasis i) u else 0 := by
  classical
  rw [← HilbertBasis.repr_apply_apply]
  change angularBasis.repr (angularBasis.repr.symm _) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (if p i then (1 : ℝ) else 0) * angularBasis.repr u i = _
  rw [HilbertBasis.repr_apply_apply]
  split_ifs <;> simp

theorem nativeAngularProjection_apply_norm_le (p : AngularIndex → Prop) (u : AngularL2) :
    ‖nativeAngularProjection p u‖ ≤ ‖u‖ := by
  classical
  change ‖angularBasis.repr.symm
    (spectralDiagonal (fun i => if p i then (1 : ℝ) else 0)
      (by norm_num : (0 : ℝ) ≤ 1) (fun i => by split_ifs <;> norm_num) (angularBasis.repr u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖spectralDiagonal (fun i => if p i then (1 : ℝ) else 0)
        (by norm_num : (0 : ℝ) ≤ 1) (fun i => by split_ifs <;> norm_num)‖ * ‖angularBasis.repr u‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖angularBasis.repr u‖ := mul_le_mul_of_nonneg_right
      (spectralDiagonal_norm_le _ _ _) (norm_nonneg _)
    _ = ‖u‖ := by rw [one_mul, LinearIsometryEquiv.norm_map]

theorem nativeAngularProjection_norm_le (p : AngularIndex → Prop) :
    ‖nativeAngularProjection p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  simpa only [one_mul] using nativeAngularProjection_apply_norm_le p u

def nativeHighProjection : AngularL2 →L[ℝ] AngularL2 :=
  nativeAngularProjection (fun i => 6 ≤ angularEigenvalue i)

def nativeLowProjection : AngularL2 →L[ℝ] AngularL2 :=
  nativeAngularProjection (fun i => angularEigenvalue i < 6)

theorem nativeHighProjection_add_low (u : AngularL2) :
    nativeHighProjection u + nativeLowProjection u = u := by
  classical
  apply angularBasis.repr.injective
  ext i
  simp only [map_add, lp.coeFn_add, Pi.add_apply, HilbertBasis.repr_apply_apply]
  rw [nativeHighProjection, nativeLowProjection,
    nativeAngularProjection_coefficient, nativeAngularProjection_coefficient]
  by_cases h : 6 ≤ angularEigenvalue i
  · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
  · rw [if_neg h, if_pos (lt_of_not_ge h), zero_add]

/-- A true bounded continuous native source projection. -/
def nativeProjectedSource (p : AngularIndex → Prop) (F : ℝ →ᵇ AngularL2) : ℝ →ᵇ AngularL2 :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => nativeAngularProjection p (F t))
    ((nativeAngularProjection p).continuous.comp F.continuous) ‖F‖
    (fun t => (nativeAngularProjection_apply_norm_le p (F t)).trans (F.norm_coe_le_norm t))

theorem nativeProjectedSource_norm_le (p : AngularIndex → Prop) (F : ℝ →ᵇ AngularL2) :
    ‖nativeProjectedSource p F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro t
  exact (nativeAngularProjection_apply_norm_le p (F t)).trans (F.norm_coe_le_norm t)

theorem nativeProjectedSource_coefficient (p : AngularIndex → Prop)
    (F : ℝ →ᵇ AngularL2) (i : AngularIndex) (t : ℝ) :
    inner ℝ (angularBasis i) (nativeProjectedSource p F t) =
      if p i then inner ℝ (angularBasis i) (F t) else 0 :=
  nativeAngularProjection_coefficient p (F t) i

theorem nativeProjectedSource_coefficient_smooth (p : AngularIndex → Prop)
    (F : ℝ →ᵇ AngularL2)
    (hF : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (F t))) (i : AngularIndex) :
    ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (nativeProjectedSource p F t)) := by
  classical
  simp_rw [nativeProjectedSource_coefficient]
  by_cases h : p i
  · simpa only [if_pos h] using hF i
  · simpa only [if_neg h] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))

end Yamabe3.Analysis.Delaunay
