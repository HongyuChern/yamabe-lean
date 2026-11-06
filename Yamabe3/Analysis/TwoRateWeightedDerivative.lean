import Yamabe3.Analysis.TwoRateKernelInverse

/-!
# The exact weighted two-rate derivative

The derivative is the difference of the two genuine exponential tails.
This exact scalar identity will identify coordinates of an already
constructed Hilbert-valued derivative convolution.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set Filter MeasureTheory
open scoped Topology

namespace Yamabe3.Analysis.Delaunay

theorem weighted_twoRateInverse_hasDerivAt {k δ : ℝ}
    (hk : 0 < k) (hδ : |δ| < k) {F : ℝ → ℝ} (hF : Continuous F)
    {A : ℝ} (hbound : ∀ s, |F s| ≤ A) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (δ * s) * twoRateInverse (k + δ) (k - δ) F s)
      (Real.exp (δ * t) *
        ((Real.exp (-(k + δ) * t) * leftTail (fun y => Real.exp ((k + δ) * y) * F y) t -
          Real.exp ((k - δ) * t) * rightTail (fun y => Real.exp (-(k - δ) * y) * F y) t) / 2)) t := by
  have hp : 0 < k + δ := by linarith [(abs_lt.mp hδ).1]
  have hm : 0 < k - δ := by linarith [(abs_lt.mp hδ).2]
  let L := fun s => Real.exp (-(k + δ) * s) *
    leftTail (fun y => Real.exp ((k + δ) * y) * F y) s
  let R := fun s => Real.exp ((k - δ) * s) *
    rightTail (fun y => Real.exp (-(k - δ) * y) * F y) s
  have hL : HasDerivAt L (-(k + δ) * L t + F t) t := by
    have htail : HasDerivAt (leftTail (fun y => Real.exp ((k + δ) * y) * F y))
        (Real.exp ((k + δ) * t) * F t) t :=
      leftTail_hasDerivAt
        (show Continuous (fun y => Real.exp ((k + δ) * y) * F y) from by fun_prop)
        (fun s => (exp_source_integrable hp hF hbound s).1) t
    have he : Real.exp (-(k + δ) * t) * Real.exp ((k + δ) * t) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    apply ((((hasDerivAt_id t).const_mul (-(k + δ))).exp).mul htail).congr_deriv
    dsimp only [id_eq, L, Function.comp_apply, Pi.mul_apply]
    nlinarith [congrArg (fun q : ℝ => q * F t) he]
  have hR : HasDerivAt R ((k - δ) * R t - F t) t := by
    have htail : HasDerivAt (rightTail (fun y => Real.exp (-(k - δ) * y) * F y))
        (-(Real.exp (-(k - δ) * t) * F t)) t :=
      rightTail_hasDerivAt
        (show Continuous (fun y => Real.exp (-(k - δ) * y) * F y) from by fun_prop)
        (fun s => (exp_source_integrable hm hF hbound s).2) t
    have he : Real.exp ((k - δ) * t) * Real.exp (-(k - δ) * t) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    apply ((((hasDerivAt_id t).const_mul (k - δ)).exp).mul htail).congr_deriv
    dsimp only [id_eq, R, Function.comp_apply, Pi.mul_apply, Pi.neg_apply]
    nlinarith [congrArg (fun q : ℝ => q * F t) he]
  have hU : HasDerivAt (twoRateInverse (k + δ) (k - δ) F)
      ((-(k + δ) * L t + (k - δ) * R t) / (-(2 * k))) t := by
    have h := (hL.add hR).div_const (-(2 * k))
    convert! h using 1
    · funext s
      dsimp only [twoRateInverse, L, R]
      congr 1
      ring
    · ring
  have h := ((((hasDerivAt_id t).const_mul δ).exp).mul hU)
  apply h.congr_deriv
  change _ = Real.exp (δ * t) * ((L t - R t) / 2)
  have hformula : twoRateInverse (k + δ) (k - δ) F t = (L t + R t) / (-(2 * k)) := by
    dsimp only [twoRateInverse, L, R]
    congr 1
    ring
  rw [hformula]
  dsimp only [id_eq]
  field_simp
  <;> ring

#print axioms weighted_twoRateInverse_hasDerivAt

end Yamabe3.Analysis.Delaunay
