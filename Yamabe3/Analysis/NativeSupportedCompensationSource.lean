import Yamabe3.Analysis.NativeFiniteShellNativeSource
import Yamabe3.Analysis.NativeOriginalFixedFarCutoffBalance

/-! The actual computed exterior compensation constructs ONE native L2
source before all tests. The outer cutoff is moved by its proved dual
identity; no arbitrary residual is declared to be a compensation. The
original baseline/correction compensation rows are retained verbatim. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable {g:RiemannianMetric 3 M} {gE:RiemannianMetric 3 E} {e:OpenPartialHomeomorph E M}
  {he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source}
  {hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target}
  {R₀:ℝ} {hsource:closedBall (0:E) R₀⊆e.source}
  {P:NativeHighPotential}
  {hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ}
  {v:ℝ→ℝ} {hv:Continuous v} {hb:∀t,0 ≤ v t ∧ v t ≤ 1}
  {τ cTail:ℝ} {ht:0 < τ} {m n:ℕ} {b S CR CM:ℝ}
  {χin χout:E→ℝ} {hχin:ContDiff ℝ ∞ χin} {hχout:ContDiff ℝ ∞ χout}
  {a:ℝ} {ha:0 < a} {ha1:a ≤ 1}
  (W:NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
    (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
    (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
    (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1)

 include W in
 theorem exists_nativeSupported_computed_compensation_source
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hfit:a*Real.exp (((m+n:ℕ):ℝ)/2+1)≤R₀)
    (Y:nativeSupportedSourcePairSpace b):
    let Comp:ℕ→NativeCollarL2:=fun i=>nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val
    let U:Fin (m+n)→NativeCollarL2:=fun i=>nativeCollarScalarMulCLM
      (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χout)
      (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχout).continuous (Comp i)
    ∃C:Lp ℝ 2 g.volumeMeasure,
      (C:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>∑i:Fin (m+n),nativeDensityCorrectedChartSource gE e (closedBall (0:E) R₀)
        (nativePhysicalShellSource a (nativeOuterLogShellCenter i) (U i)) y) ∧
      ∀(η:EnergyTest g.leviCivitaData univ)(φ:E→ℝ)(hφ:ContDiff ℝ ∞ φ)
        (hc:HasCompactSupport φ)(h0:(0:E)∉tsupport φ),
        (∀y∈closedBall (0:E) R₀,φ (a⁻¹ • y)=η (e y)) →
        let ψ:E→ℝ:=fun y=>χout (Real.exp S • y)*φ y
        let hψ:ContDiff ℝ ∞ ψ:=(hχout.comp (contDiff_id.const_smul _)).mul hφ
        let hcψ:HasCompactSupport ψ:=hc.mul_left
        let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
        inner ℝ C (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ))=
          8*a*(∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i) (Comp i))
            (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ)):=by
  dsimp only
  let Comp:ℕ→NativeCollarL2:=fun i=>nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val
  let U:Fin (m+n)→NativeCollarL2:=fun i=>nativeCollarScalarMulCLM
    (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χout)
    (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχout).continuous (Comp i)
  have hf(i:Fin (m+n)):∀y:E,Real.exp (nativeOuterLogShellCenter i-Real.log a) • y∈nativeSourceShell→y∈closedBall (0:E) R₀:=by
    intro y hy
    have hi:(i.val:ℝ)+1≤((m+n:ℕ):ℝ):=by exact_mod_cast i.isLt
    have hs:-nativeOuterLogShellCenter i+1/2≤((m+n:ℕ):ℝ)/2+1:=by
      dsimp only [nativeOuterLogShellCenter]
      linarith
    rw [mem_closedBall_zero_iff]
    exact (nativePhysicalShellSource_support_bounds ha _ hy).2.le.trans
      ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) ha.le).trans hfit)
  obtain ⟨C,hC,hpair⟩:=exists_nativeFiniteShell_fixed_native_source g gE e he hei (isCompact_closedBall (0:E) R₀) hsource hcoeff
    ha (m+n) (fun i=>nativeOuterLogShellCenter i) U hf
  refine ⟨C,hC,fun η φ hφ hc h0 htest=>?_⟩
  have hh:=hpair η φ hφ hc h0 htest
  apply hh.trans
  apply congrArg (fun r:ℝ=>8*a*r)
  apply Finset.sum_congr rfl
  intro i _
  exact nativeOuterCutoff_source_dual_pairing S (nativeOuterLogShellCenter i) χout hχout (Comp i) φ hφ hc h0

#print axioms exists_nativeSupported_computed_compensation_source
end Yamabe3.Analysis.SpherePolar
