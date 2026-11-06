import Yamabe3.Analysis.BanachFutureUniformJets
import Yamabe3.Analysis.NativeLowPhysicalField

/-! Uniform strong derivatives of the same actual native low curve.
The native Hilbert isometry transfers the Banach fixed point and its
derivatives. No derivative or smoothness of the input source is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ENNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace lp
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum

theorem nativeLowSolvedCurve_derivative_bounds (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2) :
    let u := fun t => nativeLowSolvedCurve v hv hb F t
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      (∀ t, ‖deriv u t‖ ≤ 8*‖F‖) ∧
      ∀ t, ‖deriv (deriv u) t‖ ≤ 48*‖F‖ := by
  dsimp only
  let A := lowAngularOperatorBCF v hv hb
  have hA : ‖A‖ ≤ 7/2 := lowAngularOperatorBCF_norm_le v hv hb
  let G := angularSourceCoordinates (nativeLowSource F)
  let w := banachFuturePotentialInverse 2 (by norm_num) A (by linarith) G
  let L : SpectralSpace AngularIndex →L[ℝ] AngularL2 :=
    angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap
  have hL (x : SpectralSpace AngularIndex) : ‖L x‖=‖x‖ := angularBasis.repr.symm.norm_map x
  have he : (fun t => nativeLowSolvedCurve v hv hb F t) = fun t => L (w t) := by
    funext t
    exact nativeLowAngularInverseCLM_apply v hv hb (by norm_num) (by norm_num) (nativeLowSource F) t
  have hw := banachFuturePotentialInverse_equation (by norm_num : (0:ℝ)<2) A (by linarith) G
  dsimp only at hw
  have hd (t : ℝ) : HasDerivAt (fun s => L (w s)) (L (deriv (fun s => w s) t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t (hw.1 t).hasDerivAt
  have he1 : deriv (fun s => L (w s)) = fun s => L (deriv (fun t => w t) s) :=
    funext (fun t => (hd t).deriv)
  have hd2 (t : ℝ) : HasDerivAt (fun s => L (deriv (fun t => w t) s))
      (L (deriv (deriv (fun t => w t)) t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t (hw.2.1 t).hasDerivAt
  have hG : ‖G‖ ≤ ‖F‖ := (angularSourceCoordinates_norm_le _).trans (nativeProjectedSource_norm_le _ F)
  have hj := banachFuturePotentialInverse_two_jets A hA G
  change ‖w‖≤2*‖G‖ ∧ (∀t, ‖deriv (fun s=>w s) t‖≤8*‖G‖) ∧
    (∀t, ‖deriv (deriv (fun s=>w s)) t‖≤48*‖G‖) at hj
  rw [he]
  refine ⟨fun t => (hd t).differentiableAt,?_,?_,?_⟩
  · rw [he1]
    exact fun t => (hd2 t).differentiableAt
  · intro t
    rw [he1,hL]
    exact (hj.2.1 t).trans (mul_le_mul_of_nonneg_left hG (by norm_num))
  · intro t
    rw [he1,(hd2 t).deriv,hL]
    exact (hj.2.2 t).trans (mul_le_mul_of_nonneg_left hG (by norm_num))

theorem nativeLowSolvedCurve_coordinate_bounds (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2) (i : AngularIndex) (t : ℝ) :
    let q := fun s => inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F s)
    ‖q t‖≤2*‖F‖ ∧ ‖deriv q t‖≤8*‖F‖ ∧ ‖deriv (deriv q) t‖≤48*‖F‖ := by
  dsimp only
  let u := fun s => nativeLowSolvedCurve v hv hb F s
  let L : AngularL2 →L[ℝ] ℝ := innerSL ℝ (angularBasis i)
  have hL (x : AngularL2) : ‖L x‖≤‖x‖ := by
    change ‖inner ℝ (angularBasis i) x‖≤‖x‖
    rw [← HilbertBasis.repr_apply_apply]
    simpa only [LinearIsometryEquiv.norm_map] using
      lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) (angularBasis.repr x) i
  have hu := nativeLowSolvedCurve_derivative_bounds v hv hb F
  dsimp only at hu
  have hd (s : ℝ) : HasDerivAt (fun y => L (u y)) (L (deriv u s)) s :=
    L.hasFDerivAt.comp_hasDerivAt s (hu.1 s).hasDerivAt
  have he1 : deriv (fun y => L (u y)) = fun y => L (deriv u y) := funext (fun s=>(hd s).deriv)
  have hd2 : HasDerivAt (fun y=>L (deriv u y)) (L (deriv (deriv u) t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t (hu.2.1 t).hasDerivAt
  change ‖L (u t)‖≤2*‖F‖ ∧ ‖deriv (fun y=>L (u y)) t‖≤8*‖F‖ ∧
    ‖deriv (deriv (fun y=>L (u y))) t‖≤48*‖F‖
  refine ⟨(hL _).trans (((nativeLowSolvedCurve v hv hb F).norm_coe_le_norm t).trans
    (nativeLowSolvedCurve_norm_le v hv hb F)),?_,?_⟩
  · rw [he1]
    exact (hL _).trans (hu.2.2.1 t)
  · rw [he1,hd2.deriv]
    exact (hL _).trans (hu.2.2.2 t)

#print axioms nativeLowSolvedCurve_derivative_bounds
#print axioms nativeLowSolvedCurve_coordinate_bounds
end Yamabe3.Analysis.Delaunay
