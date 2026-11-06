import Yamabe3.Analysis.NativeOriginalWholeOuterWeakEquation
import Yamabe3.Analysis.NativeOriginalCompensationSource
import Yamabe3.Analysis.NativeWholeExteriorTestAdapter
import Yamabe3.Analysis.NativeWholeFullBubbleCompletedPairing
import Yamabe3.Analysis.NativeFullBubbleSignedPairing
import Yamabe3.Analysis.NativeL2ReactionSource

/-! The SAME original-source SIGNED completed field satisfies its
actual native weak equation on the whole native exterior. A fixed
computed compensation and the same full reaction construct one L2
source BEFORE all tests. This is the hard compact-chart full potential;
no smooth-paper truncation or conormal acceptance is inferred. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
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

 theorem exists_nativeOriginal_signed_whole_exterior_equation
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hfit:a*Real.exp (((m+n:ℕ):ℝ)/2+1)≤R₀)
    (hfitTail:a*(Real.exp cTail+1)≤R₀) (hcTail:Real.log 128≤cTail)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (hfar:NativeH4BaselineFarRealization g gE e (closedBall (0:E) R₀) P ht a S cTail m n χout hχout Rbase)
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (O:Set E) (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero nativeWeakEuclideanD O)
    (hQ₀:∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
      (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 nativeWeakEuclideanD O (L₀ f))))
    (f:HalfEndPhysicalH2SourceGraph) (F:E→ℝ) (qi wo:ℝ×SpherePolar.S→ℝ)
    (hL₀:(toL2 nativeWeakEuclideanD O (L₀ f):E→ℝ)=ᵐ[volume]
      fun y=>χout (Real.exp S • y)*(ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y)
    (hwo:∀s:ℝ,NativeScaledJetRep (nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) s) s wo)
:
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    let Z:=nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f
    let q:=nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a
    let Comp:ℕ→NativeCollarL2:=fun i=>nativeH4OuterComputedCompensationRow P ht b i (T₀ f)+
      nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val
    let U:Fin (m+n)→NativeCollarL2:=fun i=>nativeCollarScalarMulCLM
      (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χout)
      (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχout).continuous (Comp i)
    ∃C:Lp ℝ 2 g.volumeMeasure,
      (C:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>∑i:Fin (m+n),nativeDensityCorrectedChartSource gE e (closedBall (0:E) R₀)
        (nativePhysicalShellSource a (nativeOuterLogShellCenter i) (U i)) y) ∧
    ∃FZ:Lp ℝ 2 g.volumeMeasure,
      (FZ:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>C y+8*q y*toL2 g.leviCivitaData univ Z y) ∧
      (Z,FZ)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' closedBall (0:E) a)ᶜ ∧
      (Z,FZ)∈NativeWeakEllipticDataSpace g (e '' closedBall (0:E) a)ᶜ
        (nativeJacobianPotential g (fun _:M=>0)) (nativeJacobianPotential_smooth g contMDiff_const):=by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  let Z:=nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f
  let Q:=Q₀ f+W.Q Y.val
  let q:=nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a
  let Ω:Set M:=(e '' closedBall (0:E) a)ᶜ
  have hsmall:a≤R₀:=by nlinarith only [W.receiving_fit,ha]
  have hBallS:closedBall (0:E) a⊆e.source:=(closedBall_subset_closedBall hsmall).trans hsource
  have hΩ:IsOpen Ω:=((isCompact_closedBall (0:E) a).image_of_continuousOn
    (e.continuousOn.mono hBallS)).isClosed.isOpen_compl
  obtain ⟨w,hw,hjet,vaux,hvc,hvaux,hAux,hzero,F_E,hFE,hforcedQ,hdataQ,hmain⟩:=
    exists_nativeOriginal_same_field_whole_outer_operator_equation W hcoeff hfit hfitTail hcTail Rbase hfar T₀ Q₀ O L₀ hQ₀ f F qi wo hL₀ hwo
  obtain ⟨C,hC,hCpair⟩:=exists_nativeOriginal_computed_compensation_source W hcoeff hfit Rbase (T₀ f)
  have hQrep:=nativeOriginalSameOuter_completed_whole_exterior_representation W T₀ Q₀ Rbase O L₀ hQ₀
    f F qi wo w hL₀ hwo hjet vaux hAux hzero hfit
  have hzK:=nativeOuterCutoff_realization_zero_off_chart ha W.outer_support W.far_window hzero hfit
  have hZq:MemLp (fun y=>q y*toL2 g.leviCivitaData univ Z y) 2 g.volumeMeasure:=
    nativeFullBubble_product_memLp_two g e (isCompact_closedBall (0:E) R₀) τ a _
  obtain ⟨FZ,hFZ,hFZpair⟩:=exists_nativeL2_same_field_reaction_source g q Z hZq C
  have hforced:(Z,FZ)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const Ω:=by
    intro η hη
    obtain ⟨φ,hφ,hc,h0,hsφ,htest⟩:=exists_nativeWholeExterior_smooth_test_adapter g e he R₀ hsource ha η hη
    obtain ⟨hQform,hBalance⟩:=hmain η φ hφ hc h0 hsφ htest hη
    have hsplit:=nativeGlobalFullBCF_test_split gE a (fullBubblePhasePotential τ) hvaux φ hφ.continuous hc h0
    have hvm:MemLp vaux 2 (volume:Measure E):=by simpa only [Measure.restrict_univ] using hvaux.memLp
    have hPotInt:=nativeFullBubble_whole_domain_completion_pairing g gE e he hei R₀ hsource hcoeff ha τ vaux hvm Q Ω hΩ
      hQrep η hη φ htest hzK
    have hSignedInt:=nativeOriginalSignedEnergy_full_reaction_integral W T₀ Q₀ Rbase f η
    have hZform:=nativeOriginalSignedEnergy_closed_form W T₀ Q₀ Rbase f (η:H1Zero g.leviCivitaData univ)
    have hCompPair:=hCpair η φ hφ hc h0 htest
    have hfinal:closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const Z (η:H1Zero g.leviCivitaData univ)=
        inner ℝ C (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ))+
        (∫y,8*q y*toL2 g.leviCivitaData univ Z y*η y ∂g.volumeMeasure):=by
      linear_combination hZform+hQform+hBalance-8*a*hsplit-hPotInt-hSignedInt-hCompPair
    exact hfinal.trans (hFZpair η).symm
  refine ⟨C,hC,FZ,hFZ,hforced,?_⟩
  exact nativeForcedEnergySpace_mem_data g (fun _:M=>0) contMDiff_const Ω _ _ hforced

#print axioms exists_nativeOriginal_signed_whole_exterior_equation
end Yamabe3.Analysis.SpherePolar
