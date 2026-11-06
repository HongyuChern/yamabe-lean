import Yamabe3.Analysis.NativeFullShellEquation
import Yamabe3.Analysis.NativeMatchedDelaunayCollar

/-! Full source returns use only the positive-time region on which the
same high plus low physical field satisfies its equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeMatchedDelaunay_shell_equation {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (B : NativeHighPotential) (p : DelaunayPhaseData κ)
    (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
    (n : ℕ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      ((∑ j : Fin 3,(nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp (nativeLogShellCenter n) F).2.2 j j)+
        nativeCollarPotentialMulCLM
          (delaunayPhasePotentialBCF p.orbit p.smooth.continuous p.bounded (p.phase+nativeLogShellCenter n))
          (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp (nativeLogShellCenter n) F).1)=
    nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace (nativeLogShellCenter n) F)) :=
  nativeFullShellSourceReturn_eq_of_positiveRestriction n _ _ (nativeMatchedDelaunay_physical_equation hκ0 hκ1 B p hp _ F)

#print axioms nativeMatchedDelaunay_shell_equation
end Yamabe3.Analysis.SpherePolar
