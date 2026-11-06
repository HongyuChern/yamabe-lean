import Yamabe3.Analysis.NativeExteriorGeometricResidual
import Yamabe3.Analysis.NativeRescaledMetric

/-! The computed outer physical source becomes the actual divergence
source of the same collar jet, with the physical factor eight retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Yamabe3.Analysis.GreenParametrix Delaunay
open Poincare.Analysis.Sobolev.Euclidean

theorem weakDivergenceSource_scaled_eq_flat_minus_error
    (O : Set E) (g : RiemannianMetric 3 E) (r : ℝ) (u : E → ℝ) (x : E) :
    weakDivergenceSource O (nativeScaledDivergenceMatrix g r) u x=
      weakNegativeLaplacian O u x-weakSecondOrderPerturbation O
        (nativeScaledPrincipalError g r) (nativeScaledFirstError g r) (fun _ => 0) u x := by
  have h := congrFun (nativeWeakJacobian_eq_divergence O g r (fun _ => 0) 0 u) x
  dsimp only [nativeWeakRescaledDelaunayJacobian] at h
  linarith only [h]

def nativeExteriorDivergencePotential (g : RiemannianMetric 3 E) (r : ℝ)
    (V : ℝ →ᵇ ℝ) (x : E) : ℝ :=
  r^2*nativePotentialDensity g (r • x)-g.pullbackVolumeDensity id (r • x)*nativeHalfEndPotentialCoefficient V x

theorem nativeExteriorNativeJacobian_divergence_ae (g : RiemannianMetric 3 E) (r : ℝ)
    (V : ℝ →ᵇ ℝ) (J : nativeCollarJetClosure) :
    (nativeExteriorNativeJacobianCLM g r V J.val : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      fun x => 8*(weakDivergenceSource nativePoissonEntranceCollar (nativeScaledDivergenceMatrix g r) J.val.1 x+
        nativeExteriorDivergencePotential g r V x*(J.val.1 : E → ℝ) x) := by
  filter_upwards [nativeExteriorNativeJacobian_weak_ae g r V J] with x hx
  rw [hx,weakDivergenceSource_scaled_eq_flat_minus_error]
  simp only [nativeExteriorDivergencePotential]
  ring

theorem nativeCollarJet_original_outer_source (g : RiemannianMetric 3 E) (r : ℝ)
    (V : ℝ →ᵇ ℝ) (J : nativeCollarJetClosure) {f : E → ℝ}
    (heq : (nativeExteriorNativeJacobianCLM g r V J.val : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar] f) :
    weakDivergenceSource nativePoissonEntranceCollar (nativeScaledDivergenceMatrix g r) J.val.1
      =ᵐ[volume.restrict nativeNegativeEntranceCollar]
        fun x => f x/8-nativeExteriorDivergencePotential g r V x*(J.val.1 : E → ℝ) x := by
  filter_upwards [heq,nativeExteriorNativeJacobian_divergence_ae g r V J] with x hx hy
  change weakDivergenceSource nativePoissonEntranceCollar (nativeScaledDivergenceMatrix g r) J.val.1 x=_
  linarith only [hx,hy]

#print axioms weakDivergenceSource_scaled_eq_flat_minus_error
#print axioms nativeExteriorNativeJacobian_divergence_ae
#print axioms nativeCollarJet_original_outer_source
end Yamabe3.Analysis.SpherePolar
