import Yamabe3.Analysis.NativeOriginalCoreFullReactionBalance
import Yamabe3.Analysis.NativeFiniteOuterOperatorRealization
import Yamabe3.Analysis.NativeOuterOperatorWindowExtension
import Yamabe3.Analysis.NativeOriginalActualOuterOperatorBalance
import Yamabe3.Analysis.NativeOriginalOuterLocalData
import Yamabe3.Analysis.NativeFiniteOuterOpenAnnulus

/-! A test-independent H2 coordinate realization of the SAME actual
original-source exterior field satisfies the genuine full-space weak
operator/core/return balance. The remaining native H1 representation
and paper-potential identification are separate acceptance obligations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
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

 theorem exists_nativeOriginal_same_field_finite_outer_data
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
    let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    let J:ℝ→nativeCollarJetClosure:=fun s=>nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) s+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s
    ∃w:ℝ×SpherePolar.S→ℝ,Measurable w ∧ (∀s:ℝ,NativeScaledJetRep (J s) s w) ∧
    ∃vaux:E→ℝ,HasCompactSupport vaux ∧ MemWkp 2 2 vaux univ ∧
      EqOn vaux (fun y=>χout (Real.exp S • y)*cylinderLift w y) (nativePolarTimeWindow (Ioc (-((m+n:ℕ):ℝ)/2) 0)) ∧
      (∀y:E,χout (Real.exp S • y)=0→vaux y=0) ∧
      ∃F_E:Lp ℝ 2 (volume:Measure E),
        (F_E:E→ℝ)=ᵐ[volume]((closedBall (0:E) R₀).indicator
          (nativeWeakConformalDensity (ball (0:E) (R₀+1)) gE (fun y:E=>vaux (a⁻¹ • y)))) ∧
        let F_N:=nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hsource F_E
        (Q₀ f+W.Q Y.val,F_N)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const
          (e '' nativeFiniteOuterOpenAnnulus a (m+n)) ∧
        (Q₀ f+W.Q Y.val,F_N)∈NativeWeakEllipticDataSpace g (e '' nativeFiniteOuterOpenAnnulus a (m+n))
          (nativeJacobianPotential g (fun _:M=>0)) (nativeJacobianPotential_smooth g contMDiff_const) ∧
      ∀(η:EnergyTest g.leviCivitaData univ)(φ:E→ℝ)(hφ:ContDiff ℝ ∞ φ)
        (hc:HasCompactSupport φ)(h0:(0:E)∉tsupport φ),
        tsupport φ⊆{y:E|1<‖y‖} →
        (∀y∈closedBall (0:E) R₀,φ (a⁻¹ • y)=η (e y)) →
        let ψ:E→ℝ:=fun y=>χout (Real.exp S • y)*φ y
        let hψ:ContDiff ℝ ∞ ψ:=(hχout.comp (contDiff_id.const_smul _)).mul hφ
        let hcψ:HasCompactSupport ψ:=hc.mul_left
        let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
        closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
          (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val)
          (η:H1Zero g.leviCivitaData univ)+
          8*a*(∫y:E,(nativeWeakRescaledDelaunayJacobian univ gE a (fun _=>0) 0 vaux y-
            gE.pullbackVolumeDensity id (a • y)*nativeHalfEndPotentialCoefficient (fullBubblePhasePotential τ) y*vaux y)*φ y)-
          closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const R.val (η:H1Zero g.leviCivitaData univ)=
          8*a*(∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
            (nativeH4OuterComputedCompensationRow P ht b i (T₀ f)+
              nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val)) (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ))-
          (∫y,8*nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y*(1-W.core y)*
            toL2 g.leviCivitaData univ R.val y*η y ∂g.volumeMeasure):=by
  dsimp only
  obtain ⟨w,hw,hjet,vaux,hvc,hvaux,he,hzero,hbalance⟩:=
    exists_nativeOriginal_actual_outer_core_operator_balance W hcoeff hfit hfitTail hcTail Rbase hfar (T₀ f)
  obtain ⟨F_E,hFE,hforced,hdata⟩:=nativeOriginalSameOuter_actual_local_data W hcoeff T₀ Q₀ Rbase O L₀ hQ₀
    f F qi wo w hL₀ hwo hjet vaux hvaux he (nativeFiniteOuterOpenAnnulus a (m+n))
    (nativeFiniteOuterOpenAnnulus_open a (m+n)) (nativeFiniteOuterOpenAnnulus_chart_fit ha (m+n) hfit)
    (fun x hx=>nativeFiniteOuterOpenAnnulus_unit_window ha (m+n) hx)
  exact ⟨w,hw,hjet,vaux,hvc,hvaux,he,hzero,F_E,hFE,hforced,hdata,hbalance⟩

#print axioms exists_nativeOriginal_same_field_finite_outer_data
end Yamabe3.Analysis.SpherePolar
