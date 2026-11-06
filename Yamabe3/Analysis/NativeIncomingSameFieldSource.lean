import Yamabe3.Analysis.NativeIncomingPotentialWindowSource
import Yamabe3.Analysis.NativeIncomingCommutatorSource
import Yamabe3.Analysis.NativeHomogeneousH4Return
import Yamabe3.Analysis.NativeSupportedOuterSourceInjection

/-! An actual incoming source producer on the genuine complete native
homogeneous field space. The SAME field supplies its real low/H4 jet and
its L6 potential part; both sources land in one complete supported pair.
The core radius parameter and tail cutoff parameter are independent;
this prevents a circular receiving-radius choice. This does not by itself
assert total PDE feedback cancellation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic Delaunay
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def incomingSameFieldH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] incomingSameFieldH1Normed

theorem exists_nativeIncoming_same_field_supported_source
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0 < R₀) (hsource:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (τ c cTail:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hχrange:∀x:E,0 ≤ χ x ∧ χ x ≤ 1)
    (h1:∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1))
    (O:Set E) (hO:MeasurableSet O) (hvol:volume O < ⊤) (hOR:O⊆ball (0:E) (Real.exp cTail+1))
    (m:ℕ) (hm:cTail < (m:ℝ)/2) (b:ℝ) (hb:b ≤ -(m:ℝ)/2-1)
    (hbc:b ≤ nativeIncomingCutoffSlice.1-1/2) :
    ∃δ C:ℝ,0 < δ ∧ 0 ≤ C ∧ ∀a:ℝ,
      Real.log 128 ≤ c → 0 < a → a ≤ 1/2 → a*Real.exp c/2 ≤ R₀ → a*Real.exp c/8 < δ →
      (∀x∈O,a • x∈K) →
      ∀(B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B),
      let Ω:=e '' ball (0:E) (a*Real.exp c/2)
      ∀hΩ:IsOpen Ω,(∀x∈Ω,B x=0) →
      ∃(J:nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] RegularLowH4Space)
        (U:H1Zero g.leviCivitaData univ →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ))
        (T:nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] nativeSupportedSourcePairSpace b),
        ‖T‖ ≤ C*Real.exp (-Real.log a/2) ∧
        (∀W,EqOn (regularLowH4Field (J W))
          (fun x:E=>nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • x)))
          (closedBall (0:E) 4)) ∧
        (∀W,(T W).val=(0,U W.val+nativeIncomingCommutatorSourceCLM gE a χ hχ (J W))) ∧
        ∀W (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ),
          inner ℝ (U W) (nativePhysicalPairTestL2 φ hφ hc h0)=
            ∫x in O,nativeIncomingPotentialCoefficient gE a τ cTail χ x*
              toL2 g.leviCivitaData univ W (e (a • x))*φ x := by
  obtain ⟨δ,D,hδ,hD,hret⟩:=exists_nativeHomogeneous_H4_return g hY gE e he hei hR₀ hsource hcoeff hB hρ
  obtain ⟨L,hL,hcomm⟩:=exists_nativeIncoming_commutator_source_uniform_bound gE hB hρ χ hχ
  obtain ⟨N,hN,hpot⟩:=exists_nativeIncoming_potential_window_source_CLM g hY gE e he hei hK hKs
    τ cTail χ hχ.continuous hχrange h1 O hO hvol hOR m hm
  refine ⟨δ,N+L*D,hδ,by positivity,?_⟩
  intro a hc ha ha1 hfit hscale hKO B hBs
  dsimp only
  intro hΩ hzero
  obtain ⟨J,hJ,hJv⟩:=hret c a hc ha hfit hscale B hBs hΩ hzero
  obtain ⟨U,hU,hUs,hUv⟩:=hpot a ha hKO
  let I:=(nativeHomogeneousEnergySpace g B hBs (e '' ball (0:E) (a*Real.exp c/2))).subtypeL
  let A:=nativeIncomingCommutatorSourceCLM gE a χ hχ
  let S:=U.comp I+A.comp J
  have hs (W:nativeHomogeneousEnergySpace g B hBs (e '' ball (0:E) (a*Real.exp c/2))):
      ∀ᵐt:ℝ∂volume,t < b → S W t=0 := by
    filter_upwards [hUs W.val,nativeIncomingCommutatorSource_time_support gE a χ hχ (J W),
      Lp.coeFn_add (U W.val) (A (J W))] with t hp ht hsum
    intro htb
    change (U W.val+A (J W):Lp AngularSpectralSpace 2 (volume:Measure ℝ)) t=0
    rw [hsum]
    change U W.val t+A (J W) t=0
    have hn:t∉Icc (nativeIncomingCutoffSlice.1-1/2) (nativeIncomingCutoffSlice.1+1/2) :=
      fun h=>not_lt_of_ge (hbc.trans h.1) htb
    rw [hp (htb.trans_le hb),ht hn,add_zero]
  let T:=nativeSupportedOuterSourceInjection b S hs
  have hS:‖S‖ ≤ (N+L*D)*Real.exp (-Real.log a/2) := by
    apply S.opNorm_le_bound (by positivity)
    intro W
    change ‖U W.val+A (J W)‖ ≤ _
    have h0:=U.le_of_opNorm_le hU W.val
    have h1:‖A (J W)‖ ≤ L*(D*Real.exp (-Real.log a/2)*‖W‖) :=
      (A.le_of_opNorm_le (hcomm a ha.le ha1) (J W)).trans
        (mul_le_mul_of_nonneg_left (J.le_of_opNorm_le hJ W) hL.le)
    apply (norm_add_le _ _).trans
    apply (add_le_add h0 h1).trans_eq
    change N*Real.exp (-Real.log a/2)*‖W.val‖+
      L*(D*Real.exp (-Real.log a/2)*‖W.val‖)=_
    change _=(N+L*D)*Real.exp (-Real.log a/2)*‖W.val‖
    ring
  refine ⟨J,U,T,(nativeSupportedOuterSourceInjection_norm b S hs).trans hS,hJv,?_,hUv⟩
  intro W
  rfl

#print axioms exists_nativeIncoming_same_field_supported_source
end Yamabe3.Analysis.SpherePolar
