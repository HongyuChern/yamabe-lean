import Yamabe3.Analysis.NativeWeakDivergenceJacobian
import Yamabe3.Analysis.NativeHalfEndSourceRegularity
import Yamabe3.Analysis.SobolevLocalCompactExtension

/-! The same corrected physical weak solution gains local H4 from its
actual original H2 source. This is an interior result; it supplies no
unproved H4 boundary trace or uniform global graph bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
local notation "O" => (Metric.ball (0:E) 1 \ {(0:E)})

theorem nativeWeakJacobian_interior_H4 (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ→ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) {u f : E→ℝ}
    (hu : MemWkpLocally 2 u O) (hf : MemWkpLocally 2 f O)
    (he : ∀U : Set E,IsOpen U → IsCompact (closure U) → closure U⊆O →
      nativeWeakRescaledDelaunayJacobian U g r v phase u=ᵐ[volume.restrict U] f) :
    MemWkpLocally 4 u O := by
  intro x hx
  have hx0 : x≠0 := by simpa using hx.2
  have hxn : ‖x‖<1 := by simpa using hx.1
  let t := -Real.log ‖x‖
  have ht : 0<t := neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr hx0) hxn)
  let W := cylinderAnnulus (t/2) (t+1)
  have hxW : x∈W := mem_cylinderAnnulus_of_log_norm hx0 (by change t/2<t;linarith) (by change t<t+1;linarith)
  have hW : IsOpen W := isOpen_cylinderAnnulus _ _
  have hWc : IsCompact (closure W) := isCompact_closure_cylinderAnnulus _ _
  have hWO : closure W⊆O := closure_positive_cylinderAnnulus_subset_halfEnd (by linarith)
  have hsub : W⊆O := subset_closure.trans hWO
  have huW := memWkp_on_precompact_of_locally hu hW hWc hWO
  let Q := fun y => -(annularDelaunayPotential v phase y+nativeDelaunayPotentialError g r v phase y)
  have hQ : ContDiffOn ℝ ∞ Q ({0}ᶜ : Set E) := by
    intro y hy
    exact ((contDiffAt_annularDelaunayPotential hv phase hy).add
      (contDiffAt_nativeDelaunayPotentialError g r hv phase hy)).neg.contDiffWithinAt
  have hweak := nativeWeakJacobian_divergence_equation hW g r v phase huW (he W hW hWc hWO)
  have heq : WeakEquation W (matrixFlux (nativeScaledDivergenceMatrix g r) (fun j => chosenWeakPartial' 2 j u W))
      (fun y => f y+Q y*u y) := by
    simpa only [Q,neg_mul,sub_eq_add_neg] using hweak
  have hh := memWkpLocally_four_of_local_potential_H2_source
    isClosed_singleton.isOpen_compl hW hWc
    (fun y hy => cylinderShell_ne_zero (closure_cylinderAnnulus_subset_shell _ _ hy))
    (fun i j => (contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r))
    (fun y _ => nativeScaledDivergenceMatrix_posDef g r y) hQ
    (hf.restrict hW hsub) huW.memLp
    (fun i => chosenWeakPartial'_memLp_of_mem huW.memW1p i)
    (fun i => chosenWeakPartial'_isWeakPartial_of_mem huW.memW1p i) heq
  obtain ⟨N,hN,hxN,hNW,huN⟩ := hh x hxW
  exact ⟨N,hN,hxN,hNW.trans hsub,huN⟩

theorem nativeOriginalSource_interior_H4 (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ→ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) (f : HalfEndPhysicalH2SourceGraph) {u : E→ℝ}
    (hu : MemWkpLocally 2 u O)
    (he : ∀U : Set E,IsOpen U → IsCompact (closure U) → closure U⊆O →
      nativeWeakRescaledDelaunayJacobian U g r v phase u=ᵐ[volume.restrict U]
        (fun y => halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) y/8)) :
    MemWkpLocally 4 u O := by
  apply nativeWeakJacobian_interior_H4 g r v hv phase hu _ he
  simpa only [div_eq_mul_inv,mul_comm] using
    (halfEndH2SourceGraph_physical_local_H2 f).smooth_mul (contDiff_const (c:=(8:ℝ)⁻¹))

#print axioms nativeWeakJacobian_interior_H4
#print axioms nativeOriginalSource_interior_H4
end Yamabe3.Analysis.UniformElliptic
