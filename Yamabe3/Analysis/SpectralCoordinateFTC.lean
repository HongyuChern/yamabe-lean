import Yamabe3.Analysis.SpectralConvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Strong Hilbert derivatives from an actual continuous derivative curve

A continuous candidate in the true lp Hilbert space, whose coordinates
are the scalar derivatives, is integrated in that Hilbert space.  Coordinate
evaluation commutes with the Bochner interval integral and separates points.
The resulting genuine fundamental theorem identifies the strong derivative.
There is no inference from coordinate differentiability alone.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology lp

namespace Yamabe3.Analysis.Delaunay

theorem hasDerivAt_spectral_of_continuous_coordinate_derivative
    {ι : Type*} {U V : ℝ → SpectralSpace ι} (hV : Continuous V)
    (hcoord : ∀ t i, HasDerivAt (fun s => U s i) (V t i) t) (t : ℝ) :
    HasDerivAt U (V t) t := by
  have hFTC (s : ℝ) : (∫ r in t..s, V r) = U s - U t := by
    ext i
    let ev := lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i
    have hEval : (∫ r in t..s, ev (V r)) = ev (∫ r in t..s, V r) :=
      ev.intervalIntegral_comp_comm (hV.intervalIntegrable _ _)
    change ev (∫ r in t..s, V r) = U s i - U t i
    rw [← hEval]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hcoord r i)
    exact (ev.continuous.comp hV).intervalIntegrable _ _
  have heq : (fun s => U t + ∫ r in t..s, V r) = U := by
    funext s
    rw [hFTC]
    abel
  have hd : HasDerivAt (fun s => ∫ r in t..s, V r) (V t) t :=
    intervalIntegral.integral_hasDerivAt_right (hV.intervalIntegrable _ _)
      hV.aestronglyMeasurable.stronglyMeasurableAtFilter hV.continuousAt
  simpa only [heq] using hd.const_add (U t)

#print axioms hasDerivAt_spectral_of_continuous_coordinate_derivative

end Yamabe3.Analysis.Delaunay
