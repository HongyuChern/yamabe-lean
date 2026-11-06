import Yamabe3.Analysis.NativeSupportedPairNewtonOperators
import Yamabe3.Analysis.NativeCollarCutoffCommutator
import Yamabe3.Analysis.NativePhysicalShellSourceCLM

/-! A genuine bounded linear far-cutoff source of the SAME supported
outer field, with critical gain sqrt(a)*exp(s/2). The shell restriction
is explicit; identifying it with a whole cutoff residual also requires
the cutoff's derivative support, proved separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay SphereSpectrum
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private instance cutoffSource65:Fact (1≤(6/5:ℝ≥0∞)) := ⟨one_le_sixFifths⟩

theorem exists_nativeSupported_cutoff_source_CLM
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    ∃S C:ℝ,S ≤ -(1/2:ℝ) ∧ 0 ≤ C ∧ ∀a:ℝ,0 < a → ∀s:ℝ,s ≤ S →
      ∃T:nativeSupportedSourcePairSpace b →L[ℝ] Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure,
        ‖T‖ ≤ C*Real.sqrt a*Real.exp (s/2) ∧ ∀X:nativeSupportedSourcePairSpace b,
          let U:=nativeCollarCutoffCommutatorCLM χ hχ
            (nativeSupportedOuterAllScaleJet b ht X.val.2
              (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
              (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val)
              (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X.val) s).val
          MemLp (nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U)) 2 g.volumeMeasure ∧
          (T X:M→ℝ)=ᵐ[g.volumeMeasure]nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U) := by
  obtain ⟨S,CJ,hS,hCJ,hjet⟩:=exists_nativeSupportedPair_Newton_all_scale_CLM P hp v hv hb b ht
  obtain ⟨DS,hDS,hsender⟩:=exists_nativePhysicalShellSource_critical_CLM g gE e he hei hK hKs
  let A:=nativeCollarCutoffCommutatorCLM χ hχ
  refine ⟨S,DS*‖A‖*CJ,hS,by positivity,fun a ha s hs=>?_⟩
  obtain ⟨J,hJ,hJv⟩:=hjet s hs
  obtain ⟨N,hN,hNv⟩:=hsender a ha s
  let U:=A.comp (nativeCollarJetClosure.subtypeL.comp J)
  let T:=N.comp U
  have hbound (X:nativeSupportedSourcePairSpace b):
      ‖T X‖ ≤ (DS*‖A‖*CJ*Real.sqrt a*Real.exp (s/2))*‖X‖ := by
    have hJX:‖J X‖ ≤ (CJ*Real.exp (5*s/2))*‖X‖ := J.le_of_opNorm_le hJ X
    have hUX:‖U X‖ ≤ ‖A‖*((CJ*Real.exp (5*s/2))*‖X‖) :=
      (A.le_opNorm (J X).val).trans (mul_le_mul_of_nonneg_left hJX (norm_nonneg A))
    have hNX:‖N (U X)‖ ≤ (DS*Real.sqrt a*Real.exp (-2*s))*‖U X‖ := N.le_of_opNorm_le hN (U X)
    apply (hNX.trans (mul_le_mul_of_nonneg_left hUX (by positivity))).trans_eq
    rw [show s/2=(-2*s)+(5*s/2) by ring,Real.exp_add]
    ring
  refine ⟨T,T.opNorm_le_bound (by positivity) hbound,?_⟩
  intro X
  have hh:=hNv (U X)
  dsimp only [U,ContinuousLinearMap.comp_apply] at hh
  rw [hJv X] at hh
  simpa [T,U,A,hJv X] using hh

#print axioms exists_nativeSupported_cutoff_source_CLM
end Yamabe3.Analysis.SpherePolar
