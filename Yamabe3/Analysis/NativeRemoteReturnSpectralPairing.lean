import Yamabe3.Analysis.NativeRemoteReturnFarSource
import Yamabe3.Analysis.NativeOriginalTotalFarClosedSource
import Yamabe3.Analysis.NativeClosedJetFarSourcePairing
import Yamabe3.Analysis.NativePhysicalShellSupport

/-! Exact spectral pairing of the SAME actual total return on a native
smooth test. Shell/source support, the chart scale, density and test
representative are all checked. The tail remains an explicit reaction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
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

 theorem nativeRemoteReturn_actual_spectral_pairing
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hfit:a*Real.exp (((m+n:ℕ):ℝ)/2+1)≤R₀)
    (Y:nativeSupportedSourcePairSpace b)
    (Rbase:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (F:Lp ℝ 2 g.volumeMeasure)
    (hbase:∀η:H1Zero g.leviCivitaData univ,
      closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const Rbase.val η=
        ∫y,(F y+8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*
          toL2 g.leviCivitaData univ Rbase.val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)
    (η:EnergyTest g.leviCivitaData univ)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ)
    (htest:∀y∈closedBall (0:E) R₀,φ (a⁻¹ • y)=η (e y)):
    let R:=Rbase+W.R Y
    let J:ℝ→nativeCollarJetClosure:=nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val
    let t:Fin n→ℝ:=fun i=>nativeOuterLogShellCenter (m+i.val)
    let C:=nativeCollarCutoffCommutatorCLM χout hχout (J S).val
    let G:Fin n→NativeCollarL2:=fun i=>nativeBCFCollarErrorCLM gE (a*Real.exp (-t i))
      (boundedTimeTranslate ℝ (t i) (fullBubblePhasePotential τ))
      (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (t i) χout)
        (nativeOuterFieldCutoffAtScale_smooth S (t i) hχout) (J (t i))).val
    closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const R.val (η:H1Zero g.leviCivitaData univ)=
      inner ℝ F (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ))+
      8*a*inner ℝ (nativeFullShellSourceReturnCLM S C) (nativePhysicalPairTestL2 φ hφ hc h0)+
      8*a*(∑i:Fin n,inner ℝ (nativeFullShellSourceReturnCLM (t i) (G i)) (nativePhysicalPairTestL2 φ hφ hc h0))+
      (∫y,8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*
        toL2 g.leviCivitaData univ R.val y)*η y ∂g.volumeMeasure):=by
  dsimp only
  let R:=Rbase+W.R Y
  let J:ℝ→nativeCollarJetClosure:=nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val
  let t:Fin n→ℝ:=fun i=>nativeOuterLogShellCenter (m+i.val)
  let C:=nativeCollarCutoffCommutatorCLM χout hχout (J S).val
  let G:Fin n→NativeCollarL2:=fun i=>nativeBCFCollarErrorCLM gE (a*Real.exp (-t i))
    (boundedTimeTranslate ℝ (t i) (fullBubblePhasePotential τ))
    (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (t i) χout)
      (nativeOuterFieldCutoffAtScale_smooth S (t i) hχout) (J (t i))).val
  let q:=nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a))
  have hf(s:ℝ)(hs:-s+1/2≤((m+n:ℕ):ℝ)/2+1):
      ∀y:E,Real.exp (s-Real.log a) • y∈nativeSourceShell→y∈closedBall (0:E) R₀:=by
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact (nativePhysicalShellSource_support_bounds ha s hy).2.le.trans
      ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) ha.le).trans hfit)
  have hfS:=hf S (by linarith [W.far_window])
  have hft(i:Fin n):-t i+1/2≤((m+n:ℕ):ℝ)/2+1:=by
    have hi:(m:ℝ)+(i.val:ℝ)+1≤((m+n:ℕ):ℝ):=by exact_mod_cast Nat.add_le_add_left (Nat.succ_le_of_lt i.isLt) m
    dsimp only [t,nativeOuterLogShellCenter]
    push_cast
    push_cast at hi
    linarith
  have hq:MemLp (fun y=>q y*toL2 g.leviCivitaData univ R.val y) 2 g.volumeMeasure:=
    nativeBubbleTail_product_memLp_two g e (isCompact_closedBall (0:E) R₀) τ cTail (Real.log a) _
  have hpair:=nativeClosedJetFarSource_actual_pairing g gE e he hei (isCompact_closedBall (0:E) R₀) hsource hcoeff
    ha S t C G hfS (fun i=>hf (t i) (hft i)) q R.val hq η φ hφ hc h0 htest
  have hweak:=nativeRemoteReturn_closed_jet_far_equation W Y Rbase F hbase (η:H1Zero g.leviCivitaData univ)
  have hη:(toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ):M→ℝ)=ᵐ[g.volumeMeasure](η:M→ℝ):=by
    rw [toL2_coe]
    exact η.memLp.coeFn_toLp
  let fr:M→ℝ:=nativeClosedJetFarSource g gE e (closedBall (0:E) R₀) a S t C G q R.val
  have hfr:MemLp fr 2 g.volumeMeasure:=nativeClosedJetFarSource_memLp_two g gE e he hei
    (isCompact_closedBall (0:E) R₀) hsource a S t C G τ cTail R.val
  have hiF:= (Lp.memLp F).integrable_mul (Lp.memLp (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ)))
  have hiR:=hfr.integrable_mul (Lp.memLp (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ)))
  have hFinner:(∫y,F y*toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ) y ∂g.volumeMeasure)=
      inner ℝ F (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ)):=by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun y=>by simp only [Real.inner_apply] <;> ring
  have hfrη:(∫y,fr y*toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ) y ∂g.volumeMeasure)=
      ∫y,fr y*η y ∂g.volumeMeasure:=by
    apply integral_congr_ae
    exact hη.mono (fun y hy=>congrArg (fun z:ℝ=>fr y*z) hy)
  apply hweak.trans
  change (∫y,(F y+fr y)*toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ) y ∂g.volumeMeasure)=_
  calc
    _=(∫y,F y*toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ) y ∂g.volumeMeasure)+
      (∫y,fr y*toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ) y ∂g.volumeMeasure):=by
      simpa only [Pi.add_apply,Pi.mul_apply,add_mul] using integral_add hiF hiR
    _=_:=by
      rw [hFinner,hfrη]
      have hh:=hpair
      dsimp only [fr,R,J,C,G,t,q] at hh ⊢
      linear_combination hh

#print axioms nativeRemoteReturn_actual_spectral_pairing
end Yamabe3.Analysis.SpherePolar
