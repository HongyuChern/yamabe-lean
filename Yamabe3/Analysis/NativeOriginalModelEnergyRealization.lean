import Yamabe3.Analysis.NativeOriginalSignedEnergy

/-! Explicit same-source model identity used by the final signed native
energy producer. This proposition grants no existence by definition. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD

def NativeOriginalModelEnergyRealization
    {κ:ℝ} (hκ0:0 ≤ κ) (hκ1:κ < 1) (p:DelaunayPhaseData κ)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|) ≤ κ)
    {τ:ℝ} (ht:0 < τ) (χ:E→ℝ) (S₀:ℝ) (O:Set E)
    (T:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (L:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero Deuc O) : Prop :=
    let P:=p.nativeHighPotential hκ0 hκ1
∀f:HalfEndPhysicalH2SourceGraph,∃F:E→ℝ,∃hF2:ContDiffOn ℝ 2 F ({0}ᶜ:Set E),
        EqOn (nativeH4GraphFunction (T f)) F (closedBall (0:E) 4) ∧
        (F=ᵐ[volume.restrict (ball (0:E) 1\{0})]fullModelPhysicalField hκ0 hκ1 p f) ∧
        ∃qi wo:ℝ×SpherePolar.S→ℝ,Measurable qi ∧ Measurable wo ∧
          (∀i:HalfEndPhysicalSliceIndex,
            ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T f)).val.1:E→ℝ)
              =ᵐ[volume.restrict nativePoissonEntranceCollar]
                fun x=>Real.exp (3*i.val/2)*(F (Real.exp (-i.val) • x)+cylinderLift qi (Real.exp (-i.val) • x))) ∧
          (∀s:ℝ,NativeScaledJetRep (nativeH4MatchedExteriorAllScaleJet P ht (T f) s) s wo) ∧
          (toL2 Deuc O (L f):E→ℝ)=ᵐ[volume]
            fun y=>χ (Real.exp S₀ • y)*(ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y

end Yamabe3.Analysis.SpherePolar
