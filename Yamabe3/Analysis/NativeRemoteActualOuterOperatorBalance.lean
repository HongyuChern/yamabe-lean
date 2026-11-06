import Yamabe3.Analysis.NativeRemoteCoreFullReactionBalance
import Yamabe3.Analysis.NativeOriginalCoreFullReactionBalance
import Yamabe3.Analysis.NativeFiniteOuterOperatorRealization
import Yamabe3.Analysis.NativeOuterOperatorWindowExtension

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

 theorem exists_nativeRemote_actual_outer_core_operator_balance
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hfit:a*Real.exp (((m+n:ℕ):ℝ)/2+1)≤R₀)
    (hfitTail:a*(Real.exp cTail+1)≤R₀) (hcTail:Real.log 128≤cTail)
    (Y:nativeSupportedSourcePairSpace b)
    (Rbase:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (Fsrc:Lp ℝ 2 g.volumeMeasure)
    (hFix:Y.val=nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a Y.val-(W.I (Rbase+W.R Y)).val)
    (hbase:∀η:H1Zero g.leviCivitaData univ,
      closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const Rbase.val η=
        ∫y,(Fsrc y+8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*
          toL2 g.leviCivitaData univ Rbase.val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure):
    let R:=Rbase+W.R Y
    let J:ℝ→nativeCollarJetClosure:=nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val
    ∃w:ℝ×SpherePolar.S→ℝ,Measurable w ∧ (∀s:ℝ,NativeScaledJetRep (J s) s w) ∧
    ∃vaux:E→ℝ,HasCompactSupport vaux ∧ MemWkp 2 2 vaux univ ∧
      EqOn vaux (fun y=>χout (Real.exp S • y)*cylinderLift w y) (nativePolarTimeWindow (Ioc (-((m+n:ℕ):ℝ)/2) 0)) ∧
      (∀y:E,χout (Real.exp S • y)=0→vaux y=0) ∧
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
            (nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val)) (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ))-
          (∫y,8*nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y*(1-W.core y)*
            toL2 g.leviCivitaData univ R.val y*η y ∂g.volumeMeasure)-
          inner ℝ Fsrc (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ)):=by
  dsimp only
  let R:=Rbase+W.R Y
  let J:ℝ→nativeCollarJetClosure:=nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val
  obtain ⟨wi,w,hwi,hw,hji,hjet,hE⟩:=W.model_field Y.val
  obtain ⟨vaux,hvc,hvaux,he,hzero,hops⟩:=exists_nativeFinite_outer_actual_weak_operator J (cylinderLift w) hjet
    χout hχout W.outer_compact S (m+n) gE a (fullBubblePhasePotential τ)
  refine ⟨w,hw,hjet,vaux,hvc,hvaux,he,hzero,fun η φ hφ hc h0 hsφ htest=>?_⟩
  have hop:=(hops φ hφ hc h0).trans (nativeOuterCompactOperator_window_to_global gE a (fullBubblePhasePotential τ)
    hvaux S hzero W.outer_support (m+n) W.far_window φ hsφ)
  have hbalance:=nativeRemote_actual_core_full_reaction_balance W hcoeff hfit hfitTail hcTail Y Rbase Fsrc hFix hbase η φ hφ hc h0 hsφ htest
  let coreOp:ℝ:=closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
    (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val)
    (η:H1Zero g.leviCivitaData univ)
  let returnOp:ℝ:=closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const R.val (η:H1Zero g.leviCivitaData univ)
  exact (congrArg (fun r:ℝ=>coreOp+8*a*r-returnOp) hop.symm).trans hbalance

#print axioms exists_nativeRemote_actual_outer_core_operator_balance
end Yamabe3.Analysis.SpherePolar
