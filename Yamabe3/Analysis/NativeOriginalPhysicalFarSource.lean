import Yamabe3.Analysis.NativeAllScaleCommutatorFiniteSingle
import Yamabe3.Analysis.NativeOriginalOuterSameFieldOperator
import Yamabe3.Analysis.NativePhysicalShellSourceCLM
import Yamabe3.Analysis.NativeH4OuterCutoffGeometricWindow

/-! Actual same original field: finite cutoff commutators equal its
single fixed-S jet source; full cutoff geometric sources split into the
EXACT baseline and correction sources used by the far solvers. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet

 theorem nativeOriginal_outer_cutoff_geometric_shell_add
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0≤v t ∧ v t≤1) (b:ℝ) {τ:ℝ} (ht:0<τ)
    (gE:RiemannianMetric 3 E) (a S s:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (x:HalfEndPhysicalH4Graph) (Y:NativeTwoSidedSource):
    nativePhysicalShellSource a s (nativeBCFCollarErrorCLM gE (a*Real.exp (-s))
      (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
      (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S s χ) (nativeOuterFieldCutoffAtScale_smooth S s hχ)
        (nativeH4MatchedExteriorAllScaleJet P ht x s+
          nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y s)).val)=ᵐ[volume]
      (nativeH4OuterCutoffGeometricShell gE P ht a S s χ hχ x+
        nativeOuterCutoffGeometricShell gE P hp v hv hb b ht a S s χ hχ Y):=by
  rw [map_add,Submodule.coe_add,map_add]
  exact nativePhysicalShellSource_add_ae a s _ _

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

 theorem nativeOriginalAffine_physical_commutator_finite_single
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let J:ℝ→nativeCollarJetClosure:=fun s=>nativeH4MatchedExteriorAllScaleJet P ht x s+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s
    (fun y:E=>∑i:Fin (m+n),nativePhysicalShellSource a (nativeOuterLogShellCenter i)
      (nativeCollarCutoffCommutatorCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χout)
        (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχout) (J (nativeOuterLogShellCenter i)).val) y)=ᵐ[volume]
      nativePhysicalShellSource a S (nativeCollarCutoffCommutatorCLM χout hχout (J S).val):=by
  dsimp only
  obtain ⟨w,hw,hjet,hrows⟩:=exists_nativeOriginal_outer_same_field_operator W Rbase x
  exact nativeAllScale_cutoff_commutator_finite_eq_single _ (cylinderLift w) hjet χout hχout W.outer_derivatives a S (m+n)
    (by linarith [W.far_scale]) (by exact le_of_lt (lt_trans (by linarith: -S+1/4 < -S+1/2) W.far_window))

#print axioms nativeOriginal_outer_cutoff_geometric_shell_add
#print axioms nativeOriginalAffine_physical_commutator_finite_single
end Yamabe3.Analysis.SpherePolar
