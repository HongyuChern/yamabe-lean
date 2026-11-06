import Yamabe3.Analysis.NativeFullModelLocalH4
import Yamabe3.Analysis.WeakLaplacianEquation
import Yamabe3.Analysis.SobolevLocalCompactExtension

/-! The genuine weak negative Laplacian of the complete high-plus-low
field uses the original full source, before and after any scale change. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

theorem fullModelPhysicalField_weakNegativeLaplacian
    {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (p:DelaunayPhaseData κ)
    (f:HalfEndPhysicalH2SourceGraph) {V:Set E} (hV:IsOpen V)
    (hVc:IsCompact (closure V)) (hVO:closure V⊆O) :
    let u:=fullModelPhysicalField hκ0 hκ1 p f
    let F:=halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f)
    MemWkp 4 2 u V ∧ weakNegativeLaplacian V u =ᵐ[volume.restrict V]
      (fun x=>F x/8+nativeHalfEndPotentialCoefficient p.potential x*u x) := by
  let u:=fullModelPhysicalField hκ0 hκ1 p f
  let F:=halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f)
  let g:=fun x=>F x/8+nativeHalfEndPotentialCoefficient p.potential x*u x
  have hsub:V⊆O:=subset_closure.trans hVO
  obtain ⟨hu0,hg,du,hdu,hw,he⟩:=fullModelPhysicalField_same_weak_equation hκ0 hκ1 p f
  have huV:MemWkp 4 2 u V:=memWkp_on_precompact_of_locally
    (fullModelPhysicalField_local_H4 hκ0 hκ1 p f) hV hVc hVO
  have hgrad (i:Fin 3):du i =ᵐ[volume.restrict V] chosenWeakPartial' 2 i u V:=
    HasWeakPartialDeriv.ae_eq hV ((hw i).restrict hV hsub)
      (chosenWeakPartial'_isWeakPartial_of_mem huV.memW1p i)
      (((hdu i).mono_measure (Measure.restrict_mono hsub le_rfl)).locallyIntegrable (by norm_num))
      ((chosenWeakPartial'_memLp_of_mem huV.memW1p i).locallyIntegrable (by norm_num))
  refine ⟨huV,weakNegativeLaplacian_eq_source_ae hV (huV.le_of_le (by omega))
    ((hg.mono_measure (Measure.restrict_mono hsub le_rfl)).locallyIntegrable (by norm_num)) ?_⟩
  exact (he.restrict hsub).congr_flux hgrad

#print axioms fullModelPhysicalField_weakNegativeLaplacian
end Yamabe3.Analysis.UniformElliptic
