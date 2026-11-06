import Yamabe3.Analysis.NativeIncomingSameFieldSource
import Yamabe3.Analysis.NativeCombinedFarTailSolver

/-! Explicit predicates for the actual source/field identities already
proved by the incoming and far producers. The predicates add no proof
of existence by definition; a joint producer must construct their maps
AND proofs. They keep those identities available in the final coupling. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic Delaunay
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def feedbackCertificateH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] feedbackCertificateH1Normed

def NativeIncomingSourceRealization
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (Ω:Set M) (hΩ:IsOpen Ω) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (a τ cTail:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (O:Set E) (b:ℝ)
    (J:nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] RegularLowH4Space)
    (U:H1Zero g.leviCivitaData univ →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (I:nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] nativeSupportedSourcePairSpace b) : Prop :=
  (∀W,EqOn (regularLowH4Field (J W))
    (fun x:E=>nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • x))) (closedBall (0:E) 4)) ∧
  (∀W,(I W).val=(0,U W.val+nativeIncomingCommutatorSourceCLM gE a χ hχ (J W))) ∧
  ∀W (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ),
    inner ℝ (U W) (nativePhysicalPairTestL2 φ hφ hc h0)=
      ∫x in O,nativeIncomingPotentialCoefficient gE a τ cTail χ x*
        toL2 g.leviCivitaData univ W (e (a • x))*φ x

def NativeFarTailRealization
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (Ω:Set M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M) (K:Set E)
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)
    (a s cTail:ℝ) (n:ℕ) (t:Fin n→ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (R:nativeSupportedSourcePairSpace b →L[ℝ] nativeHomogeneousEnergySpace g B hBs Ω) : Prop :=
  ∀X:nativeSupportedSourcePairSpace b,∃w:ℝ×SpherePolar.S→ℝ,Measurable w ∧
    (∀r,(fun θ=>w (r,θ))=ᵐ[angularVolume]
      (nativeSupportedOuterCurve b ht X.val.2
        (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
        (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val) r:SpherePolar.S→ℝ)) ∧
    ∀η:H1Zero g.leviCivitaData univ,
      closedYamabeJacobianForm g B hBs (R X).val η=
        ∫y,(nativeDensityCorrectedChartSource gE e K
          (physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation s (cylinderLift w)) s a) y+
          (∑i:Fin n,nativeDensityCorrectedChartSource gE e K
            (nativeOuterCutoffGeometricShell gE P hp v hv hb b ht a s (t i) χ hχ X.val) y)+
          8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ cTail (Real.log a)) y*
            toL2 g.leviCivitaData univ (R X).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure

#print axioms NativeIncomingSourceRealization
#print axioms NativeFarTailRealization
end Yamabe3.Analysis.SpherePolar
