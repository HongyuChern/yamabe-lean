import Yamabe3.Analysis.NativePoissonEntranceLimits

/-! The actual finite physical fields have value and radial derivative
traces converging to the original entrance and true DtN data. The signs
and the conformal half-weight are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

theorem nativePoissonFiniteCollar_normal_trace_ae (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) :
    (fun θ : S => fderiv ℝ (nativePoissonFiniteCollar P b s) (θ:E) (θ:E)) =ᵐ[angularVolume]
      (⇑(finiteHilbertProjection angularBasis s (nativePoissonPhysicalEntranceNormal P b))) := by
  have hD : P.dtn b = -P.curveDerivative b 0 := rfl
  have he : (fun θ : S => fderiv ℝ (nativePoissonFiniteCollar P b s) (θ:E) (θ:E)) =
      (fun θ => projectedAngular s (fun _ => nativePoissonPhysicalEntranceNormal P b) (0,θ)) := by
    funext θ
    rw [(nativePoissonFiniteCollar_entrance P b s θ).2]
    unfold projectedAngular finiteAngular nativePoissonPhysicalEntranceNormal
    rw [hD,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [nativePoissonCoordinate,inner_sub_right,inner_neg_right,real_inner_smul_right]
    ring
  rw [he]
  exact projectedAngular_ae s (fun _ => nativePoissonPhysicalEntranceNormal P b) 0


#print axioms nativePoissonFiniteCollar_normal_trace_ae
end Yamabe3.Analysis.SpherePolar
