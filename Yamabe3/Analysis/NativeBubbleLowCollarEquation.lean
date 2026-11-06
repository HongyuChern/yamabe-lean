import Yamabe3.Analysis.NativeBubbleLowCollar
import Yamabe3.Analysis.NativePoissonExteriorCollarEquation
import Yamabe3.Analysis.BubbleLowPhysicalCauchy

/-! The actual low correction in entrance-centred coordinates solves
its compensating physical equation, with the factor 8 and source sign
retained. No restriction of a volume representative to a sphere occurs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeBubbleCollarCompensation (t₀ : ℝ) (c : AngularIndex → ℝ) : E → ℝ :=
  physicalForcing (finiteAngular nativeLowIndexFinset (fun i t => -c i*bubbleCompensation i (t₀+t)))

theorem nativeBubbleLow_shifted_equation (t₀ : ℝ) (c : AngularIndex → ℝ)
    (q : AngularIndex → ℝ → ℝ)
    (heq : ∀i∈nativeLowIndexFinset,∀t,deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t=
      -c i*bubbleCompensation i t) (i : AngularIndex) (hi : i∈nativeLowIndexFinset) (t : ℝ) :
    deriv (deriv (fun s => q i (t₀+s))) t=
      (angularEigenvalue i+1/4-nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)) t)*q i (t₀+t)-
        c i*bubbleCompensation i (t₀+t) := by
  have hd : deriv (fun s => q i (t₀+s))=fun s => deriv (q i) (t₀+s) :=
    funext fun s => deriv_comp_const_add (q i) t₀ s
  rw [hd,deriv_comp_const_add]
  have hpot : nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)) t=
      (15/4)*fullBubbleDensity (t₀+t) := by
    change (fullBubbleHighPotential (-t₀)).potential (-t)=_
    rw [fullBubble_exterior_potential,sub_neg_eq_add]
  rw [hpot]
  have h := heq i hi (t₀+t)
  unfold bubbleLowCoefficient at h
  linarith only [h]

theorem nativeBubbleLowCollar_physical_equation (t₀ : ℝ) (c : AngularIndex → ℝ)
    (q : AngularIndex → ℝ → ℝ)
    (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i))
    (heq : ∀i∈nativeLowIndexFinset,∀t,deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t=
      -c i*bubbleCompensation i t) {x : E} (hx : x≠0) :
    -8*nativeCoordinateLaplacian (finitePhysical nativeLowIndexFinset (fun i t => q i (t₀+t))) x-
      8*nativeHalfEndPotentialCoefficient (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))) x*
        finitePhysical nativeLowIndexFinset (fun i t => q i (t₀+t)) x=
      nativeBubbleCollarCompensation t₀ c x := by
  have h := native_finitePhysical_negative_trace_eq_global_C2
    (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))) nativeLowIndexFinset
    (fun i t => q i (t₀+t)) (fun i t => -c i*bubbleCompensation i (t₀+t))
    (fun i hi => (hq i hi).comp (contDiff_const.add contDiff_id))
    (fun i hi t => by
      have h := nativeBubbleLow_shifted_equation t₀ c q heq i hi t
      linarith only [h]) hx
  change -nativeCoordinateLaplacian (finitePhysical nativeLowIndexFinset (fun i t => q i (t₀+t))) x=
    nativeBubbleCollarCompensation t₀ c x/8+
      nativeHalfEndPotentialCoefficient (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))) x*
        finitePhysical nativeLowIndexFinset (fun i t => q i (t₀+t)) x at h
  linarith only [h]

#print axioms nativeBubbleLow_shifted_equation
#print axioms nativeBubbleLowCollar_physical_equation
end Yamabe3.Analysis.SpherePolar
