import Yamabe3.Analysis.NativeOriginalWholeExteriorEquation
import Yamabe3.Analysis.NativeSmoothPotentialFixedFieldEquation
import Yamabe3.Analysis.NativeSmoothPotentialFeedback
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


 def nativeFiniteCompensationSourceFunction
    (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M) (K:Set E)
    (a S:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (N:ℕ) (Comp:ℕ→NativeCollarL2):M→ℝ:=
  fun y=>∑i:Fin N,nativeDensityCorrectedChartSource gE e K
    (nativePhysicalShellSource a (nativeOuterLogShellCenter i)
      (nativeCollarScalarMulCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
        (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ).continuous (Comp i))) y

 theorem exists_nativeSmoothOriginal_same_exterior_solution
    (hY:0<Target.yamabeConstant g)
    (χSm:E→ℝ) (hSm:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (nativeScaledSmoothBubblePotential e τ a χSm))
    (q:Lp ℝ (3/2:ℝ≥0∞) g.volumeMeasure)
    (hq:(q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y-
      nativeScaledSmoothBubblePotential e τ a χSm y))
    (T:(H1Zero g.leviCivitaData univ) →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (hTw:∀z:H1Zero g.leviCivitaData univ,∀η:H1Zero g.leviCivitaData univ,
      closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (T z).val η=
        ∫y,(nativeCriticalPotentialReactionCLM g hY q z y+8*(nativeCompactChartFunction e (closedBall (0:E) R₀)
          (fullBubbleScaledTail τ cTail (Real.log a)) y*toL2 g.leviCivitaData univ (T z).val y))*
          toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)
    (JSm:H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ)
    (hJSm:∀z:H1Zero g.leviCivitaData univ,JSm z=z+nativeRemoteReturnResponseCLM W (T (JSm z)))
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
    let Y₀:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    let Z₀:=nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f
    let Z:=JSm Z₀
    let Y₁:=nativeOriginalAffineFeedbackCLM W
      (0:(nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))) →L[ℝ] nativeSupportedSourcePairSpace b)
      (ContinuousLinearMap.id ℝ _) (T Z)
    let V:M→ℝ:=fun y=>g.leviCivitaData.scalarCurvature y-8*nativeScaledSmoothBubblePotential e τ a χSm y
    let hV:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ V:=g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul hSm)
    ∃C₀ C₁:Lp ℝ 2 g.volumeMeasure,
      (C₀:M→ℝ)=ᵐ[g.volumeMeasure]nativeFiniteCompensationSourceFunction gE e (closedBall (0:E) R₀) a S χout hχout (m+n)
        (fun i=>nativeH4OuterComputedCompensationRow P ht b i (T₀ f)+nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₀.val) ∧
      (C₁:M→ℝ)=ᵐ[g.volumeMeasure]nativeFiniteCompensationSourceFunction gE e (closedBall (0:E) R₀) a S χout hχout (m+n)
        (fun i=>nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₁.val) ∧
      ∃Ft:Lp ℝ 2 g.volumeMeasure,
        (Ft:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>(C₀+C₁:Lp ℝ 2 g.volumeMeasure) y+
          8*nativeScaledSmoothBubblePotential e τ a χSm y*toL2 g.leviCivitaData univ Z y) ∧
        (Z,Ft)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' closedBall (0:E) a)ᶜ ∧
        (Z,C₀+C₁)∈NativeWeakEllipticDataSpace g (e '' closedBall (0:E) a)ᶜ V hV:=by
  dsimp only
  let Z₀:=nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f
  let Z:=JSm Z₀
  let dz:=nativeRemoteReturnResponseCLM W (T Z)
  have hEq:Z=Z₀+dz:=hJSm Z₀
  obtain ⟨C₀,hC₀,F₀,hF₀,hforced₀,hdata₀⟩:=exists_nativeOriginal_signed_whole_exterior_equation W hcoeff hfit hfitTail hcTail
    Rbase hfar T₀ Q₀ O L₀ hQ₀ f F qi wo hL₀ hwo
  obtain ⟨C₁,hC₁,F₁,hF₁,hforced₁,hdata₁⟩:=exists_nativeSmoothPotential_actual_response_equation W hY hcoeff hfit hfitTail hcTail
    χSm hSm q hq T hTw Z
  obtain ⟨Ft,hFt,hforced,hdata⟩:=nativeSmoothPotential_same_fixed_field_equation g ((e '' closedBall (0:E) a)ᶜ)
    (nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a) (nativeScaledSmoothBubblePotential e τ a χSm) hSm
    Z₀ dz Z hEq C₀ C₁ F₀ F₁ hF₀ hF₁ hforced₀ hforced₁
  exact ⟨C₀,C₁,hC₀,hC₁,Ft,hFt,hforced,hdata⟩

#print axioms exists_nativeSmoothOriginal_same_exterior_solution
end Yamabe3.Analysis.SpherePolar
