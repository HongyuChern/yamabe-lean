import Yamabe3.Analysis.NativeHomogeneousH4Return
import Yamabe3.Analysis.NativeOriginalAffineFeedback
import Yamabe3.Analysis.NativeH4InnerPartialFeedback
import Yamabe3.Analysis.NativeH4SupportedWindowSource

/-! The ACTUAL affine original-source feedback has the required inner
fixed point, since its incoming source has exactly zero first coordinate.
This discharges the partial inner cancellation premise without assuming
an obsolete full-collar exterior fixed point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
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


theorem exists_nativeActualIncoming_same_smooth_field
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))):
    ∃F:E→ℝ,ContDiff ℝ ∞ F ∧HasCompactSupport F ∧
      (∀x∈closedBall (0:E) 4,F=ᶠ[𝓝 x]
        (fun y=>nativeHomogeneousEnergyRepresentative g (fun _:M=>0) contMDiff_const W.open_domain R (e (a • y)))) ∧
      EqOn (regularLowH4Field (W.J R)) F (closedBall (0:E) 4):=by
  let Ω:=e '' ball (0:E) (a*64)
  let U:=nativeHomogeneousEnergyRepresentative g (fun _:M=>0) contMDiff_const W.open_domain R
  let T:=nativeHomogeneousChartLinear g (fun _:M=>0) contMDiff_const W.open_domain e a
  have hgeom {x:E}(hx:x∈ball (0:E) 5):a • x∈ball (0:E) (a*64):=by
    rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg ha.le]
    have hn:=mem_ball_zero_iff.mp hx
    nlinarith
  have hfit {x:E}(hx:x∈ball (0:E) 5):a • x∈e.source:=
    hsource ((closedBall_subset_closedBall W.receiving_fit) (ball_subset_closedBall (hgeom hx)))
  have hT:ContDiffOn ℝ ∞ (T R) (ball (0:E) 5):=
    nativeHomogeneousChartLinear_smooth g (fun _:M=>0) contMDiff_const W.open_domain e he a isOpen_ball
      (fun x hx=>hfit hx) (fun x hx=>mem_image_of_mem e (hgeom hx)) R
  have hval {x:E}(hx:x∈ball (0:E) 5):T R x=U (e (a • x)):=
    indicator_of_mem (mem_image_of_mem e (hgeom hx)) _
  obtain ⟨F,hF,hFc,hFe⟩:=exists_smooth_compact_extension_near_compact isOpen_ball
    (isCompact_closedBall (0:E) 4) (closedBall_subset_ball (by norm_num:(4:ℝ)<5)) hT
  have he(x:E)(hx:x∈closedBall (0:E) 4):F=ᶠ[𝓝 x](fun y=>U (e (a • y))):=by
    apply (hFe x hx).trans
    filter_upwards [isOpen_ball.mem_nhds ((closedBall_subset_ball (by norm_num:(4:ℝ)<5)) hx)] with y hy
    exact hval hy
  refine ⟨F,hF,hFc,he,fun x hx=>?_⟩
  exact (W.incoming.1 R hx).trans (he x hx).self_of_nhds.symm

#print axioms exists_nativeActualIncoming_same_smooth_field
end Yamabe3.Analysis.SpherePolar
