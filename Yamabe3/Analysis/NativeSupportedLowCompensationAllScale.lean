import Yamabe3.Analysis.NativeSupportedOuterAllScale
import Yamabe3.Analysis.NativeFiniteAllScaleEquation

/-! The finite compensation of the actual Cauchy correction at all
scales, with the original coefficients fixed once by the original source
and entrance data. The flat normalized operator retains division by 8. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeSupportedLowCompensationCoefficients (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) (i : AngularIndex) (t : ℝ) : ℝ :=
  -nativeSupportedBubbleExteriorInhomogeneousCompensation b ht (F,(d,n)) i*bubbleCompensation i (τ+t)

theorem nativeSupportedLowCauchy_ode (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) (i : AngularIndex)
    (hi : i∈nativeLowIndexFinset) (t : ℝ) :
    deriv (deriv (nativeSupportedLowCauchyCoefficients b ht F d n i)) t=
      (angularEigenvalue i+1/4-fullBubblePhasePotential τ t)*nativeSupportedLowCauchyCoefficients b ht F d n i t+
        nativeSupportedLowCompensationCoefficients b ht F d n i t := by
  let dn := nativeBubbleLowCorrectionDataCLM τ (nativeSupportedReverseSourcePrepareCLM b F,(d,n))
  let q := nativeLowCauchyQ ht (nativeLowCauchyCoordinateCLM dn)
  let c := nativeSupportedBubbleExteriorInhomogeneousCompensation b ht (F,(d,n))
  have heq (j : AngularIndex) (hj : j∈nativeLowIndexFinset) (r : ℝ) :
      deriv (deriv (q j)) r-bubbleLowCoefficient j r*q j r= -c j*bubbleCompensation j r :=
    (nativeLowCauchyQ_spec ht dn.1 dn.2 j hj).2.1 r
  have h := nativeBubbleLow_shifted_equation τ c q heq i hi t
  rw [nativeBubbleExteriorPotential_eq_phase] at h
  change deriv (deriv (fun r => q i (τ+r))) t=
    (angularEigenvalue i+1/4-fullBubblePhasePotential τ t)*q i (τ+t)+(-c i*bubbleCompensation i (τ+t))
  linarith only [h]

def nativeSupportedLowCompensationScaled (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) (s : ℝ) : E→ℝ :=
  fun x => physicalForcing (finiteAngular nativeLowIndexFinset
    (fun i => weightedTimeShift s (nativeSupportedLowCompensationCoefficients b ht F d n i))) x/8

theorem nativeSupportedLowCauchyAllScale_source (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) (s : ℝ) :
    (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
      (nativeSupportedLowCauchyAllScaleJet b ht F d n s).val : E→ℝ)
      =ᵐ[volume.restrict nativePoissonEntranceCollar] nativeSupportedLowCompensationScaled b ht F d n s :=
  nativeFiniteAllScale_flat_source (fullBubblePhasePotential τ) nativeLowIndexFinset
    (nativeSupportedLowCauchyCoefficients b ht F d n) (nativeSupportedLowCompensationCoefficients b ht F d n)
    (nativeSupportedLowCauchyCoefficients_C2 b ht F d n) (nativeSupportedLowCauchy_ode b ht F d n) s

#print axioms nativeSupportedLowCauchy_ode
#print axioms nativeSupportedLowCauchyAllScale_source
end Yamabe3.Analysis.SpherePolar
