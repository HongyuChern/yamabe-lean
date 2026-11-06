import Yamabe3.Analysis.NativePoissonCollarIdentification

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

def nativePoissonPhysicalEntranceNormal (P : NativeHighPotential) (b : AngularH1) : AngularL2 :=
  P.dtn b-(1/2:ℝ) • P.curve b 0

theorem nativePoissonFiniteCollar_value_trace_ae (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) :
    (fun θ : S => nativePoissonFiniteCollar P b s (θ:E)) =ᵐ[angularVolume]
      (⇑(finiteHilbertProjection angularBasis s (P.curve b 0))) := by
  have he : (fun θ : S => nativePoissonFiniteCollar P b s (θ:E)) =
      (fun θ => projectedAngular s (P.curve b) (0,θ)) := by
    funext θ
    simpa only [projectedAngular,finiteAngular,nativePoissonCoordinate] using (nativePoissonFiniteCollar_entrance P b s θ).1
  rw [he]
  exact projectedAngular_ae s (P.curve b) 0


#print axioms nativePoissonFiniteCollar_value_trace_ae
end Yamabe3.Analysis.SpherePolar
