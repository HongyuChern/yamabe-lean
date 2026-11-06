import Yamabe3.Analysis.NativeFiniteWindowSourceInverse
import Yamabe3.Analysis.NativeSupportedOuterShellEquation

/-! The actual native full-window equation of the SAME feedback field.
The physical low compensation is computed from that field and remains
visible. No exterior artificial-extension equation is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic
variable (P:NativeHighPotential)
  (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)

def nativeFiniteWindowOuterJet (s:ℝ) (Y:NativeTwoSidedSource):nativeCollarJetClosure :=
  nativeSupportedOuterAllScaleJet b ht Y.2 (nativeLowL2AngularCLM v hv hb Y.1 0)
    (nativeFullL2NormalAngularCLM P hp v hv hb Y.1)
    (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ Y) (nativeTwoSidedSourceSigma_regular P hp v hv hb τ Y) s

def nativeFiniteWindowOuterCompensationRow (n:ℕ) (Y:NativeTwoSidedSource):NativeCollarL2 :=
  nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter n) (fullBubblePhasePotential τ))
    (nativeSupportedLowCauchyAllScaleJet b ht Y.2 (nativeLowL2AngularCLM v hv hb Y.1 0)
      (nativeFullL2NormalAngularCLM P hp v hv hb Y.1) (nativeOuterLogShellCenter n)).val

def nativeFiniteWindowOuterJacobianRow (g:RiemannianMetric 3 E) (ε:ℝ) (n:ℕ)
    (Y:NativeTwoSidedSource):NativeCollarL2 :=
  nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter n) (fullBubblePhasePotential τ))
    (nativeFiniteWindowOuterJet P hp v hv hb b ht (nativeOuterLogShellCenter n) Y).val+
      nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht g ε n Y

theorem nativeFiniteWindowOuterJacobian_shell_source
    (g:RiemannianMetric 3 E) (ε:ℝ) (n:ℕ) (Y:NativeTwoSidedSource)
    (hYs:∀ᵐt:ℝ∂volume,t < b → Y.2 t=0) :
    nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter n)
      (nativeFiniteWindowOuterJacobianRow P hp v hv hb b ht g ε n Y)=
      -nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter n)
        (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace (nativeOuterLogShellCenter n) Y.2))+
      nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter n)
        (nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht n Y)+
      nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter n)
        (nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht g ε n Y) := by
  unfold nativeFiniteWindowOuterJacobianRow nativeFiniteWindowOuterJet
  rw [map_add,nativeSupportedOuter_shell_model_source b ht Y.2
    (nativeLowL2AngularCLM v hv hb Y.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb Y.1)
    _ _ hYs n]
  rfl

theorem nativeFiniteWindowOuterJacobian_pairing
    (m:ℕ) (g:RiemannianMetric 3 E) (ε:ℝ) (Y:NativeTwoSidedSource)
    (hYs:∀ᵐt:ℝ∂volume,t < b → Y.2 t=0)
    (G:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) :
    (∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeFiniteWindowOuterJacobianRow P hp v hv hb b ht g ε i Y)) G)=
      -(∫t in Ioc (-(m:ℝ)/2) 0,inner ℝ (Y.2 t) (G t))+
      (∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
        (nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y)) G)+
      inner ℝ (nativeFiniteOuterWindowSourceCLM m
        (fun i=>nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht g ε i) Y) G := by
  have hF:(∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace (nativeOuterLogShellCenter i) Y.2))) G)=
      ∫t in Ioc (-(m:ℝ)/2) 0,inner ℝ (Y.2 t) (G t) := by
    simpa only [nativeFiniteOuterWindowSourceCLM,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply,sum_inner] using nativeFiniteOuterWindowSource_reconstructs m Y.2 G
  have hE:(∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht g ε i Y)) G)=
      inner ℝ (nativeFiniteOuterWindowSourceCLM m
        (fun i=>nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht g ε i) Y) G := by
    simp only [nativeFiniteOuterWindowSourceCLM,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,sum_inner]
  simp_rw [nativeFiniteWindowOuterJacobian_shell_source P hp v hv hb b ht g ε _ Y hYs,
    inner_add_left,inner_neg_left]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_neg_distrib,hF,hE]

theorem nativeFiniteWindowOuter_fixed_pairing
    (m:ℕ) (g:RiemannianMetric 3 E) (ε:ℝ) (X Y:NativeTwoSidedSource)
    (hY:Y=X+nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m g ε Y)
    (hb0:b ≤ -(m:ℝ)/2-1) (hX:∀ᵐt:ℝ∂volume,t < b → X.2 t=0)
    (G:Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hG:∀ᵐt:ℝ∂volume,t∉Ioc (-(m:ℝ)/2) 0 → G t=0) :
    (∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeFiniteWindowOuterJacobianRow P hp v hv hb b ht g ε i Y)) G)=
      -inner ℝ X.2 G+
      (∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
        (nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y)) G) := by
  have hYs:=nativeFiniteWindow_fixed_preserves_lower_support P hp v hv hb b ht m g ε X Y hY hb0 hX
  have hh:=nativeFiniteWindowOuterJacobian_pairing P hp v hv hb b ht m g ε Y hYs G
  have hRestr:inner ℝ Y.2 G=∫t in Ioc (-(m:ℝ)/2) 0,inner ℝ (Y.2 t) (G t) := by
    rw [L2.inner_def,←integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [hG] with t hz
    by_cases ht:t∈Ioc (-(m:ℝ)/2) 0
    · rw [indicator_of_mem ht]
    · rw [indicator_of_notMem ht,hz ht,inner_zero_right]
  have hi:=congrArg (fun Z:NativeTwoSidedSource=>inner ℝ Z.2 G) hY
  change inner ℝ Y.2 G=inner ℝ (X.2+nativeFiniteOuterWindowSourceCLM m
    (fun i=>nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht g ε i) Y) G at hi
  rw [inner_add_left] at hi
  rw [←hRestr] at hh
  linarith only [hi,hh]

#print axioms nativeFiniteWindowOuterJacobian_shell_source
#print axioms nativeFiniteWindowOuterJacobian_pairing
#print axioms nativeFiniteWindowOuter_fixed_pairing
end Yamabe3.Analysis.SpherePolar
