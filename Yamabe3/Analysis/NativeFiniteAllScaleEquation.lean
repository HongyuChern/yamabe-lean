import Yamabe3.Analysis.NativeFiniteAllScaleField
import Yamabe3.Analysis.NativeOrbitCollarJacobian
import Yamabe3.Analysis.BubbleFinitePhysicalEquation

/-! The precise shifted inhomogeneous equation for a finite C2 angular
field. The original source receives exp(2s) before physicalForcing and the
normalization by 8 is explicit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeFiniteWeightedShift_ode (V : ℝ→ᵇ ℝ) (m : Finset AngularIndex)
    (q f : AngularIndex→ℝ→ℝ) (hq : ∀i∈m,ContDiff ℝ 2 (q i))
    (heq : ∀i∈m,∀t,deriv (deriv (q i)) t=(angularEigenvalue i+1/4-V t)*q i t+f i t)
    (s : ℝ) (i : AngularIndex) (hi : i∈m) (t : ℝ) :
    deriv (deriv (weightedTimeShift s (q i))) t=
      (angularEigenvalue i+1/4-boundedTimeTranslate ℝ s V t)*weightedTimeShift s (q i) t+
        weightedTimeShift s (f i) t := by
  rw [weightedTimeShift_second s (hq i hi)]
  change Real.exp (2*s)*deriv (deriv (q i)) (t+s)=
    (angularEigenvalue i+1/4-V (t+s))*(Real.exp (2*s)*q i (t+s))+Real.exp (2*s)*f i (t+s)
  rw [heq i hi (t+s)]
  ring

theorem nativeFiniteAllScale_flat_source (V : ℝ→ᵇ ℝ) (m : Finset AngularIndex)
    (q f : AngularIndex→ℝ→ℝ) (hq : ∀i∈m,ContDiff ℝ 2 (q i))
    (heq : ∀i∈m,∀t,deriv (deriv (q i)) t=(angularEigenvalue i+1/4-V t)*q i t+f i t)
    (s : ℝ) :
    (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s V) (nativeFiniteAllScaleJet m q hq s).val : E→ℝ)
      =ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => physicalForcing (finiteAngular m (fun i => weightedTimeShift s (f i))) x/8) := by
  let qs := fun i => weightedTimeShift s (q i)
  let fs := fun i => weightedTimeShift s (f i)
  let hqs := fun i hi => weightedTimeShift_C2 s (hq i hi)
  have h := nativeFlatCollarJet_C2_ae (boundedTimeTranslate ℝ s V)
    ⟨finitePhysical m qs,finitePhysical_contDiffOn_offZero_C2 m qs hqs⟩
  filter_upwards [h,ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx hxO
  change nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s V)
    (nativeC2CollarJetLinear ⟨finitePhysical m qs,finitePhysical_contDiffOn_offZero_C2 m qs hqs⟩) x=_
  rw [hx]
  have he := native_finitePhysical_negative_trace_eq_global_C2 (boundedTimeTranslate ℝ s V) m qs fs hqs
    (nativeFiniteWeightedShift_ode V m q f hq heq s) (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hxO))
  change -nativeCoordinateLaplacian (finitePhysical m qs) x=
    physicalForcing (finiteAngular m fs) x/8+
      nativeHalfEndPotentialCoefficient (boundedTimeTranslate ℝ s V) x*finitePhysical m qs x at he
  change -nativeCoordinateLaplacian (finitePhysical m qs) x-
    nativeHalfEndPotentialCoefficient (boundedTimeTranslate ℝ s V) x*finitePhysical m qs x=_
  linarith only [he]

#print axioms nativeFiniteWeightedShift_ode
#print axioms nativeFiniteAllScale_flat_source
end Yamabe3.Analysis.SpherePolar
