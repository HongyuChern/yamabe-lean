import Yamabe3.Analysis.NativeC2CollarSeries

/-! Linearity of the actual L2 value class for C2 collar fields.
The assertion concerns the original functions and their same restricted measure. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar

theorem nativeC2CollarValue_add {u v w : E → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) (hv : ContDiffOn ℝ 2 v ({0}ᶜ : Set E))
    (hw : ContDiffOn ℝ 2 w ({0}ᶜ : Set E)) (he : w=u+v) :
    nativeC2CollarValue hw=nativeC2CollarValue hu+nativeC2CollarValue hv := by
  apply Lp.ext
  filter_upwards [(nativeC2Collar_memLp hu).1.coeFn_toLp,(nativeC2Collar_memLp hv).1.coeFn_toLp,
    (nativeC2Collar_memLp hw).1.coeFn_toLp,Lp.coeFn_add (nativeC2CollarValue hu) (nativeC2CollarValue hv)] with x hx hy hz ha
  change nativeC2CollarValue hu x=u x at hx
  change nativeC2CollarValue hv x=v x at hy
  change nativeC2CollarValue hw x=(nativeC2CollarValue hu+nativeC2CollarValue hv) x
  calc
    _=w x := hz
    _=u x+v x := congrFun he x
    _=(nativeC2CollarValue hu+nativeC2CollarValue hv) x := by
      simpa only [Pi.add_apply,hx,hy] using ha.symm

theorem nativeC2CollarValue_smul {u w : E → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) (hw : ContDiffOn ℝ 2 w ({0}ᶜ : Set E))
    (c : ℝ) (he : w=c • u) : nativeC2CollarValue hw=c • nativeC2CollarValue hu := by
  apply Lp.ext
  filter_upwards [(nativeC2Collar_memLp hu).1.coeFn_toLp,(nativeC2Collar_memLp hw).1.coeFn_toLp,
    Lp.coeFn_smul c (nativeC2CollarValue hu)] with x hx hz ha
  change nativeC2CollarValue hu x=u x at hx
  change nativeC2CollarValue hw x=(c • nativeC2CollarValue hu) x
  calc
    _=w x := hz
    _=c • u x := congrFun he x
    _=(c • nativeC2CollarValue hu) x := by
      simpa only [Pi.smul_apply,hx] using ha.symm

#print axioms nativeC2CollarValue_add
#print axioms nativeC2CollarValue_smul
end Yamabe3.Analysis.SpherePolar
