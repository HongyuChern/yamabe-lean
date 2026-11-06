import Yamabe3.Analysis.NativeFiniteOuterCompactRealization
import Yamabe3.Analysis.NativeFiniteWeakOperatorReconstruction

/-! One test-independent compact H2 realization identifies the complete
finite cutoff operator with a genuine weak differential operator of the
SAME outer field on the retained window. No vanishing residual or
exterior Data membership is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay SphereSpectrum
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak

 theorem exists_nativeFinite_outer_actual_weak_operator
    (J:ℝ→nativeCollarJetClosure) (u:E→ℝ)
    (hJ:∀s:ℝ,(J s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s u)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (S:ℝ) (N:ℕ)
    (g:RiemannianMetric 3 E) (a:ℝ) (V:ℝ→ᵇℝ):
    ∃v:E→ℝ,HasCompactSupport v ∧ MemWkp 2 2 v univ ∧
      EqOn v (fun x=>χ (Real.exp S • x)*u x) (nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0)) ∧
      (∀x:E,χ (Real.exp S • x)=0→v x=0) ∧
      ∀(φ:E→ℝ)(hφ:ContDiff ℝ ∞ φ)(hcφ:HasCompactSupport φ)(h0:(0:E)∉tsupport φ),
        (∑i:Fin N,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
          ((nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) V)+
            nativeBCFCollarErrorCLM g (a*Real.exp (-nativeOuterLogShellCenter i))
              (boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) V))
            (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
              (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ) (J (nativeOuterLogShellCenter i))).val))
              (nativePhysicalPairTestL2 φ hφ hcφ h0))=
          ∫x in nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0),
            (nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 v x-
              g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*v x)*φ x:=by
  obtain ⟨v,hvc,hv,he,hzero,hjets⟩:=exists_nativeFinite_outer_compact_H2_realization J u hJ χ hχ hc S N
  refine ⟨v,hvc,hv,he,hzero,fun φ hφ hcφ h0=>?_⟩
  exact nativeFinite_full_BCF_global_weak_operator g a V hv N
    (fun i=>nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
      (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ) (J (nativeOuterLogShellCenter i)))
    hjets φ hφ hcφ h0

#print axioms exists_nativeFinite_outer_actual_weak_operator
end Yamabe3.Analysis.SpherePolar
