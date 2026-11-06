import Yamabe3.Analysis.NativeH4OuterSupportedIdentity
import Yamabe3.Analysis.NativeH4CollarRealization

/-! Actual Newton-rate bounded jet operators for the ORIGINAL H4
baseline outer field, with its true low Cauchy compensations. The
constant is fixed before the source and every far scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem exists_nativeH4Exterior_Newton_all_scale_CLM
    (P:NativeHighPotential) {τ:ℝ} (ht:0 < τ) :
    ∃S C:ℝ,S ≤ -(1/2:ℝ) ∧ 0 ≤ C ∧ ∀s:ℝ,s ≤ S →
      ∃J:HalfEndPhysicalH4Graph →L[ℝ] nativeCollarJetClosure,
        ‖J‖ ≤ C*Real.exp (5*s/2) ∧ ∀x,J x=nativeH4MatchedExteriorAllScaleJet P ht x s := by
  obtain ⟨S,hS,D,hD,hd⟩:=exists_nativeSupportedOuter_same_field_Newton_annulus_H4 0 ht
  let A:=nativeH4GraphAngularValueCLM.prod nativeH4GraphAngularNormalCLM
  let B:=fullBubbleHighPotential (-τ)
  let Sig:=nativeH4GraphExteriorDatumCLM B P
  let C:=D.toReal*(‖A‖+‖Sig‖)
  have hC:0 ≤ C:=by dsimp only [C];positivity
  obtain ⟨D₀,hD₀,hbase⟩:=exists_nativeH4MatchedExteriorAllScale_bound P ht
  refine ⟨S,C,hS,hC,fun s hs=>?_⟩
  obtain ⟨J,hJ,hJv⟩:=hbase s (by linarith only [hs,hS])
  refine ⟨J,J.opNorm_le_bound (by positivity) ?_,hJv⟩
  intro x
  obtain ⟨w,hw,hl,ha,hj,hreg⟩:=hd 0 (nativeH4GraphAngularValueCLM x) (nativeH4GraphAngularNormalCLM x)
    (Sig x) (nativeH4GraphExteriorDatum_regular B P x)
    (by filter_upwards [Lp.coeFn_zero (E:=AngularSpectralSpace) (p:=2) (μ:=(volume:Measure ℝ))] with t ht;exact fun _=>ht)
  let u:=weightedPhysicalDilation s (cylinderLift w)
  have hu:MemWkp 4 2 u halfEndBasicAnnulus:=(hreg s hs).1
  obtain ⟨K,hKv,hK⟩:=exists_nativeCollarJet_of_weak_H4 hu
  have he:J x=K:=by
    apply nativeCollarJet_value_injective
    apply Lp.ext
    rw [hJv,nativeH4MatchedExteriorAllScale_supported_zero P ht 0]
    exact (hj s).trans hKv.symm
  have hn:‖J x‖ ≤ (iteratedWeakSobolevNorm 4 2 u halfEndBasicAnnulus).toReal:=by rw [he];exact hK
  have hh:=ENNReal.toReal_mono (ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top) ((hreg s hs).2 4 le_rfl)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hh
  have hdata:‖((0:Lp AngularSpectralSpace 2 (volume:Measure ℝ)),
      (nativeH4GraphAngularValueCLM x,nativeH4GraphAngularNormalCLM x))‖=‖A x‖:=by
    change max ‖(0:Lp AngularSpectralSpace 2 (volume:Measure ℝ))‖ ‖A x‖=‖A x‖
    rw [norm_zero,max_eq_right (norm_nonneg _)]
  rw [hdata] at hh
  have hbnd:‖A x‖+‖Sig x‖ ≤ (‖A‖+‖Sig‖)*‖x‖:=
    (add_le_add (A.le_opNorm x) (Sig.le_opNorm x)).trans_eq (by ring)
  apply (hn.trans hh).trans
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hbnd (Real.exp_pos _).le) ENNReal.toReal_nonneg).trans_eq (by dsimp only [C];ring)

#print axioms exists_nativeH4Exterior_Newton_all_scale_CLM
end Yamabe3.Analysis.UniformElliptic
