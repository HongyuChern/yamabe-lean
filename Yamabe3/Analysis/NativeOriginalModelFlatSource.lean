import Yamabe3.Analysis.NativeFullWeakLaplacian
import Yamabe3.Analysis.NativeFullZeroSourceH2
import Yamabe3.Analysis.NativeWeakFlatLocality
import Yamabe3.Analysis.NativeTrueEntranceH4Solver

/-! An actual same-volume representative of the original full-source
model has the SAME original normalized source on each interior region.
The full source is retained; it is never projected to the high modes. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativeOriginalModel_flat_same_source
    {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (p:DelaunayPhaseData κ)
    (f:HalfEndPhysicalH2SourceGraph) (F:E→ℝ)
    (hF:F=ᵐ[volume.restrict (Metric.ball (0:E) 1\{0})]fullModelPhysicalField hκ0 hκ1 p f)
    {U:Set E} (hU:IsOpen U) (hUc:IsCompact (closure U)) (hUO:closure U⊆Metric.ball (0:E) 1\{0}) :
    MemWkp 4 2 F U ∧ nativeWeakFlatJacobian U p.orbit p.phase F=ᵐ[volume.restrict U]
      fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8 := by
  have hFU:F=ᵐ[volume.restrict U]fullModelPhysicalField hκ0 hκ1 p f:=
    ae_mono (Measure.restrict_mono (subset_closure.trans hUO) le_rfl) hF
  obtain ⟨hm,he⟩:=fullModelPhysicalField_weakNegativeLaplacian hκ0 hκ1 p f hU hUc hUO
  refine ⟨(MemWkp_congr_ae (by norm_num) hU hFU).mpr hm,?_⟩
  filter_upwards [weakNegativeLaplacian_congr_ae hU hFU,he,hFU] with x hx he hf
  change weakNegativeLaplacian U F x+annularDelaunayPotential p.orbit p.phase x*F x=_
  rw [hx,he,hf,fullModelPotential_eq_neg_annular]
  change _/8+-annularDelaunayPotential p.orbit p.phase x*fullModelPhysicalField hκ0 hκ1 p f x+
    annularDelaunayPotential p.orbit p.phase x*fullModelPhysicalField hκ0 hκ1 p f x=_
  ring

#print axioms nativeOriginalModel_flat_same_source
end Yamabe3.Analysis.SpherePolar
