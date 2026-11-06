import Yamabe3.Analysis.NativeHalfEndGraphEquation
import Yamabe3.Analysis.WeakLaplacianEquation
import Yamabe3.Analysis.SobolevLocalCompactExtension

/-! The actual weak negative Laplacian of the original field equals its
original normalized source plus potential, on every precompact subdomain.
The weak equation is produced from the half-end solver, not assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

theorem nativeHalfEndH2Source_weakNegativeLaplacian
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (P : ℝ →ᵇ ℝ)
    (hP : ∀ t, (∫ s : ℝ, spectralMajorant (5/2) (-2) s*|P (t-s)|) ≤ κ)
    (hP0 : ∀ t, 0 ≤ P t) (hPs : ContDiff ℝ ∞ (fun t : ℝ => P t))
    (f : HalfEndHighH2Source) {V : Set E} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O) :
    let u := cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 P hP hP0 f)
    let F := halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1)
    MemWkp 4 2 u V ∧ weakNegativeLaplacian V u =ᵐ[volume.restrict V]
      (fun x => F x/8+nativeHalfEndPotentialCoefficient P x*u x) := by
  let u := cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 P hP hP0 f)
  let F := halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1)
  let g := fun x => F x/8+nativeHalfEndPotentialCoefficient P x*u x
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have hsub : V ⊆ O := subset_closure.trans hVO
  obtain ⟨hu0,hu4,hg,du,hdu,hvar,-,-,-⟩ :=
    nativeHalfEndH2Source_same_variational_equation hκ0 hκ1 P hP hP0 hPs f
  have huV : MemWkp 4 2 u V := memWkp_on_precompact_of_locally hu4 hV hVc hVO
  have heq : WeakEquation O (fun i => (du i : E → ℝ)) g := by
    intro φ hφ hc hs
    have hm : MemH01 φ O := memW01p_of_contDiff_hasCompactSupport_subset hO hφ hc hs
    have hp (i : Fin 3) : MemLp (partialDeriv i φ) 2 (volume.restrict O) :=
      ((contDiff_partial hφ i).continuous.memLp_of_hasCompactSupport
        (hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))).restrict O
    have hw (i : Fin 3) : HasWeakPartialDeriv i (partialDeriv i φ) φ O :=
      HasWeakPartialDeriv.of_contDiff hO (hφ.of_le (by norm_cast))
    exact (hvar φ hm (fun i => partialDeriv i φ) hp hw).2.2
  have heqV := heq.restrict hsub
  have hgrad (i : Fin 3) : (du i : E → ℝ) =ᵐ[volume.restrict V] chosenWeakPartial' 2 i u V :=
    HasWeakPartialDeriv.ae_eq hV ((hdu i).restrict hV hsub)
      (chosenWeakPartial'_isWeakPartial_of_mem huV.memW1p i)
      (((Lp.memLp (du i)).mono_measure (Measure.restrict_mono hsub le_rfl)).locallyIntegrable (by norm_num))
      ((chosenWeakPartial'_memLp_of_mem huV.memW1p i).locallyIntegrable (by norm_num))
  refine ⟨huV,weakNegativeLaplacian_eq_source_ae hV (huV.le_of_le (by omega))
    ((hg.mono_measure (Measure.restrict_mono hsub le_rfl)).locallyIntegrable (by norm_num)) ?_⟩
  exact heqV.congr_flux hgrad

#print axioms nativeHalfEndH2Source_weakNegativeLaplacian
end Yamabe3.Analysis.UniformElliptic
