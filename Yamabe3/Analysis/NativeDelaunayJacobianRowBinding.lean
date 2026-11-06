import Yamabe3.Analysis.NativeOrbitCollarJacobian
import Yamabe3.Analysis.NativeGlobalJacobianRows
import Yamabe3.Analysis.NativeActualHighPoissonRegularity

/-! The model potential and the geometric error use the same original
Delaunay orbit and phase, on the same true all-scale half-end jet. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem delaunayPhasePotential_time_translate {κ : ℝ} (p : DelaunayPhaseData κ) (s : ℝ) :
    boundedTimeTranslate ℝ s p.potential=
      delaunayPhasePotentialBCF p.orbit p.smooth.continuous p.bounded (p.phase+s) := by
  ext t
  change (15/4)*p.orbit (t+s+p.phase)^4=(15/4)*p.orbit (t+(p.phase+s))^4
  rw [show t+s+p.phase=t+(p.phase+s) by ring]

theorem nativeDelaunayJacobianRow_same_operator {κ : ℝ} (p : DelaunayPhaseData κ)
    (hκ0 : 0≤κ) (hκ1 : κ<1)
    (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|) ≤ κ)
    (g : RiemannianMetric 3 E) (ε s : ℝ) :
    nativeHalfGeometricJacobianRowCLM (p.nativeHighPotential hκ0 hκ1) hp g ε p.orbit p.smooth p.phase s=
      (nativeOrbitCollarJacobianCLM g (ε*Real.exp (-s)) p.orbit p.smooth p.bounded (p.phase+s)).comp
        (nativeL2HalfAllScaleRawJetCLM (p.nativeHighPotential hκ0 hκ1) hp s) := by
  apply ContinuousLinearMap.ext
  intro F
  simp only [nativeHalfGeometricJacobianRowCLM,nativeHalfModelJacobianRowCLM,
    nativeOrbitCollarJacobianCLM,nativeFlatCollarJetCLM,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply,nativeL2HalfGeometricRowCLM]
  change -((∑ j : Fin 3,nativeL2HalfAllScaleSecond (p.nativeHighPotential hκ0 hκ1) hp s F j j)+
      nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s p.potential)
        (nativeL2HalfAllScaleValue (p.nativeHighPotential hκ0 hκ1) hp s F))+_=
    -((∑ j : Fin 3,nativeL2HalfAllScaleSecond (p.nativeHighPotential hκ0 hκ1) hp s F j j)+
      nativeCollarPotentialMulCLM (delaunayPhasePotentialBCF p.orbit p.smooth.continuous p.bounded (p.phase+s))
        (nativeL2HalfAllScaleValue (p.nativeHighPotential hκ0 hκ1) hp s F))+_
  rw [delaunayPhasePotential_time_translate]

#print axioms delaunayPhasePotential_time_translate
#print axioms nativeDelaunayJacobianRow_same_operator
end Yamabe3.Analysis.SpherePolar
