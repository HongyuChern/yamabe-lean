import Yamabe3.Analysis.NativeOriginalOuterLocalRepresentation
import Yamabe3.Analysis.NativeGlobalH2ChartSourceCanonical
import Yamabe3.Analysis.NativeForcedEnergyDataMembership

/-! The SAME baseline-plus-feedback completion actually belongs to
native local weak Data, with an explicitly constructed L2 source. The
H2 source is computed; neither a weak PDE nor Data membership is an
input. Its identification with the prescribed exterior source is still
an independent obligation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 4096
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak
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

 theorem nativeOriginalSameOuter_actual_local_data
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (O:Set E) (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero nativeWeakEuclideanD O)
    (hQ₀:∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
      (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 nativeWeakEuclideanD O (L₀ f))))
    (f:HalfEndPhysicalH2SourceGraph) (F:E→ℝ) (qi wo w:ℝ×SpherePolar.S→ℝ)
    (hL₀:(toL2 nativeWeakEuclideanD O (L₀ f):E→ℝ)=ᵐ[volume]
      fun y=>χout (Real.exp S • y)*(ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y)
    (hwo:∀s:ℝ,NativeScaledJetRep (nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) s) s wo)
    (hw:∀s:ℝ,NativeScaledJetRep
      (nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) s+
        nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht
          (nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)).val s) s w)
    (vaux:E→ℝ) (hvaux:MemWkp 2 2 vaux univ)
    (hAux:EqOn vaux (fun y=>χout (Real.exp S • y)*cylinderLift w y)
      (nativePolarTimeWindow (Ioc (-((m+n:ℕ):ℝ)/2) 0)))
    (A:Set E) (hA:IsOpen A) (hAK:A⊆closedBall (0:E) R₀)
    (hAunit:∀x∈A,a⁻¹ • x∈nativePolarTimeWindow (Ioc (-((m+n:ℕ):ℝ)/2) 0) ∧ 1<‖a⁻¹ • x‖):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    ∃F_E:Lp ℝ 2 (volume:Measure E),
      (F_E:E→ℝ)=ᵐ[volume]((closedBall (0:E) R₀).indicator
        (nativeWeakConformalDensity (ball (0:E) (R₀+1)) gE (fun y:E=>vaux (a⁻¹ • y)))) ∧
      let F_N:=nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hsource F_E
      (Q₀ f+W.Q Y.val,F_N)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' A) ∧
      (Q₀ f+W.Q Y.val,F_N)∈NativeWeakEllipticDataSpace g (e '' A) (nativeJacobianPotential g (fun _:M=>0))
        (nativeJacobianPotential_smooth g contMDiff_const):=by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  have hu:MemWkp 2 2 (fun y:E=>vaux (a⁻¹ • y)) univ:=by
    simpa only [preimage_univ] using memWkp_comp_dilation (inv_ne_zero ha.ne') isOpen_univ
      (by norm_num:(1:ℝ≥0∞)≤2) 2 hvaux
  have hrep:=nativeOriginalSameOuter_completed_local_representation W T₀ Q₀ Rbase O L₀ hQ₀ f F qi wo w hL₀ hwo hw
    vaux hAux A hA hAK hAunit
  obtain ⟨F_E,hFE,hforced⟩:=nativeGlobalH2_chart_canonical_density_source g gE e he hei R₀ hsource hcoeff hA hAK
    (fun y:E=>vaux (a⁻¹ • y)) hu (Q₀ f+W.Q Y.val) hrep
  refine ⟨F_E,hFE,hforced,?_⟩
  exact nativeForcedEnergySpace_mem_data g (fun _:M=>0) contMDiff_const (e '' A) _ _ hforced

#print axioms nativeOriginalSameOuter_actual_local_data
end Yamabe3.Analysis.SpherePolar
