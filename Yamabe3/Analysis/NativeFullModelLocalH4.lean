import Yamabe3.Analysis.NativeFullModelWeakEquation
import Yamabe3.Analysis.NativeHalfEndH4Regularity
import Yamabe3.Analysis.NativeHalfEndSourceRegularity

/-! The same full-source high-plus-low physical field is locally H4.
The genuine weak equation uses the original H2 source; no regularity
of the two projected H2 sources is assumed or inferred. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

theorem fullModelPhysicalField_local_H4 {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1)
    (p:DelaunayPhaseData κ) (f:HalfEndPhysicalH2SourceGraph) :
    MemWkpLocally 4 (fullModelPhysicalField hκ0 hκ1 p f) O := by
  let u:=fullModelPhysicalField hκ0 hκ1 p f
  let F:=halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f)
  have hO:IsOpen O:=Metric.isOpen_ball.sdiff isClosed_singleton
  obtain ⟨hu,-,du,hdu,hw,heq⟩:=fullModelPhysicalField_same_weak_equation hκ0 hκ1 p f
  have hf:MemWkpLocally 2 (fun x=>F x/8) O:=by
    simpa only [div_eq_mul_inv,mul_comm] using
      (halfEndH2SourceGraph_physical_local_H2 f).smooth_mul (contDiff_const (c:=(8:ℝ)⁻¹))
  intro x hx
  have hx0:x≠0:=by simpa using hx.2
  have hxn:‖x‖<1:=by simpa using hx.1
  let t:=-Real.log ‖x‖
  have ht:0<t:=neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr hx0) hxn)
  let W:=cylinderAnnulus (t/2) (t+1)
  have hxW:x∈W:=mem_cylinderAnnulus_of_log_norm hx0 (by change t/2<t;linarith)
    (by change t<t+1;linarith)
  have hW:IsOpen W:=isOpen_cylinderAnnulus _ _
  have hWO:closure W⊆O:=closure_positive_cylinderAnnulus_subset_halfEnd (by linarith)
  have hsub:W⊆O:=subset_closure.trans hWO
  have heW:WeakEquation W (matrixFlux (fun _:E=>(1:Matrix (Fin 3) (Fin 3) ℝ)) du)
      (fun x=>F x/8+nativeHalfEndPotentialCoefficient p.potential x*u x):=by
    intro φ hφ hc hs
    have hh:=(heq.restrict hsub) φ hφ hc hs
    simpa [matrixFlux,Matrix.one_apply] using hh
  have hh:=memWkpLocally_four_of_local_potential_H2_source
    (A:=fun _:E=>(1:Matrix (Fin 3) (Fin 3) ℝ))
    isClosed_singleton.isOpen_compl hW (isCompact_closure_cylinderAnnulus _ _)
    (fun y hy=>cylinderShell_ne_zero (closure_cylinderAnnulus_subset_shell _ _ hy))
    (fun _ _=>contDiff_const) (fun _ _=>Matrix.PosDef.one)
    (nativeHalfEndPotentialCoefficient_contDiffOn p.potential p.potential_smooth)
    (hf.restrict hW hsub) (hu.1.mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun i=>(hdu i).mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun i=>(hw i).restrict hW hsub) heW
  obtain ⟨N,hN,hxN,hNW,hreg⟩:=hh x hxW
  exact ⟨N,hN,hxN,hNW.trans hsub,hreg⟩

#print axioms fullModelPhysicalField_local_H4
end Yamabe3.Analysis.UniformElliptic
