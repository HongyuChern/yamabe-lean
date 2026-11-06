import Yamabe3.Analysis.NativeOriginalCoreFullReactionBalance
import Yamabe3.Analysis.NativeFiniteOuterOperatorRealization
import Yamabe3.Analysis.NativeOuterOperatorWindowExtension
import Yamabe3.Analysis.NativeOriginalActualOuterOperatorBalance
import Yamabe3.Analysis.NativeOriginalOuterLocalData
import Yamabe3.Analysis.NativeFiniteOuterOpenAnnulus
import Yamabe3.Analysis.NativeOriginalJointOuterData
import Yamabe3.Analysis.NativeCompactH2NativeSourcePairing
import Yamabe3.Analysis.NativeCompactH2CanonicalDomainSource
import Yamabe3.Analysis.NativeOriginalWholeExteriorRepresentation
import Yamabe3.Analysis.NativeOuterAuxiliaryCompactSupport

/-! A test-independent H2 coordinate realization of the SAME actual
original-source exterior field satisfies the genuine full-space weak
operator/core/return balance. The remaining native H1 representation
and paper-potential identification are separate acceptance obligations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option diagnostics true
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

 theorem exists_nativeOriginal_same_field_whole_outer_operator_equation
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
        (F_E:E→ℝ)=ᵐ[volume]nativeWeakConformalDensity univ gE (fun y:E=>vaux (a⁻¹ • y)) ∧
        let F_N:=nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hsource F_E
        (Q₀ f+W.Q Y.val,F_N)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const
          (e '' closedBall (0:E) a)ᶜ ∧
        (Q₀ f+W.Q Y.val,F_N)∈NativeWeakEllipticDataSpace g (e '' closedBall (0:E) a)ᶜ
          (nativeJacobianPotential g (fun _:M=>0)) (nativeJacobianPotential_smooth g contMDiff_const) ∧
      ∀(η:EnergyTest g.leviCivitaData univ)(φ:E→ℝ)(hφ:ContDiff ℝ ∞ φ)
        (hc:HasCompactSupport φ)(h0:(0:E)∉tsupport φ),
        tsupport φ⊆{y:E|1<‖y‖} →
        (∀y∈closedBall (0:E) R₀,φ (a⁻¹ • y)=η (e y)) →
        tsupport (η:M→ℝ)⊆(e '' closedBall (0:E) a)ᶜ →
        let ψ:E→ℝ:=fun y=>χout (Real.exp S • y)*φ y
        let hψ:ContDiff ℝ ∞ ψ:=(hχout.comp (contDiff_id.const_smul _)).mul hφ
        let hcψ:HasCompactSupport ψ:=hc.mul_left
        let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
        (closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (Q₀ f+W.Q Y.val) (η:H1Zero g.leviCivitaData univ)=
          8*a*(∫y:E,nativeWeakRescaledDelaunayJacobian univ gE a (fun _=>0) 0 vaux y*φ y)) ∧
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
  obtain ⟨w,hw,hjet,vaux,hvc,hvaux,hAux,hzero,hbalance⟩:=
    exists_nativeOriginal_actual_outer_core_operator_balance W hcoeff hfit hfitTail hcTail Rbase hfar (T₀ f)
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  let Ω:Set M:=(e '' closedBall (0:E) a)ᶜ
  have hsmall:a≤R₀:=by nlinarith only [W.receiving_fit,ha]
  have hBallS:closedBall (0:E) a⊆e.source:=(closedBall_subset_closedBall hsmall).trans hsource
  have hΩ:IsOpen Ω:=((isCompact_closedBall (0:E) a).image_of_continuousOn
    (e.continuousOn.mono hBallS)).isClosed.isOpen_compl
  have hQrep:=nativeOriginalSameOuter_completed_whole_exterior_representation W T₀ Q₀ Rbase O L₀ hQ₀
    f F qi wo w hL₀ hwo hjet vaux hAux hzero hfit
  have hU:MemWkp 2 2 (fun y:E=>vaux (a⁻¹ • y)) univ:=by
    simpa only [preimage_univ] using memWkp_comp_dilation (inv_ne_zero ha.ne') isOpen_univ
      (by norm_num:(1:ℝ≥0∞)≤2) 2 hvaux
  obtain ⟨hpos,hrad,hSupp⟩:=nativeOuterAuxiliary_retained_support_radius ha W.outer_support hzero W.far_window hfit
  have hzU(y:E)(hy:y∉closedBall (0:E) (a*Real.exp ((1/4:ℝ)-S))):vaux (a⁻¹ • y)=0:=
    image_eq_zero_of_notMem_tsupport (f:=fun z:E=>vaux (a⁻¹ • z)) (fun h=>hy (hSupp h))
  have hzK(y:E)(hy:y∉closedBall (0:E) R₀):vaux (a⁻¹ • y)=0:=
    hzU y (fun h=>hy ((closedBall_subset_closedBall hrad.le) h))
  obtain ⟨F_E,hFE,hforced⟩:=nativeCompactH2_canonical_domain_actual_source g gE e he hei hrad hsource hcoeff
    (fun y:E=>vaux (a⁻¹ • y)) hU hzU Ω hΩ (Q₀ f+W.Q Y.val) hQrep
  have hdata:=nativeForcedEnergySpace_mem_data g (fun _:M=>0) contMDiff_const Ω _ _ hforced
  refine ⟨w,hw,hjet,vaux,hvc,hvaux,hAux,hzero,F_E,hFE,hforced,hdata,fun η φ hφ hc h0 hsφ htest hη=>?_⟩
  refine ⟨?_,hbalance η φ hφ hc h0 hsφ htest⟩
  exact (hforced η hη).trans (nativeCompactH2_native_source_physical_pairing g gE e he hei R₀ hsource hcoeff ha
    vaux hvaux F_E hFE η φ htest hzK)

#print axioms exists_nativeOriginal_same_field_whole_outer_operator_equation
end Yamabe3.Analysis.SpherePolar
