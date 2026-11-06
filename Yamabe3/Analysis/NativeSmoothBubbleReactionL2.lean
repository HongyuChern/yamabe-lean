import Yamabe3.Analysis.NativeSmoothBubbleResidualSupport
import Yamabe3.Analysis.NativeFullBubbleSignedPairing

/-! The SAME critical reaction has a genuine native L2 representative
at every fixed scale. This is not a uniform small L2 estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

 theorem exists_nativeSmoothBubble_same_reaction_L2
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g)
    (e:OpenPartialHomeomorph E M) {K:Set E} (hK:IsCompact K) (τ a:ℝ) (χ:E→ℝ)
    (hSm:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (nativeScaledSmoothBubblePotential e τ a χ))
    (q:Lp ℝ (3/2:ℝ≥0∞) g.volumeMeasure)
    (hq:(q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e K τ a y-nativeScaledSmoothBubblePotential e τ a χ y))
    (z:H1Zero g.leviCivitaData univ):
    ∃F:Lp ℝ 2 g.volumeMeasure,
      (F:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>8*((nativeScaledFullBubblePotential e K τ a y-
        nativeScaledSmoothBubblePotential e τ a χ y)*toL2 g.leviCivitaData univ z y)) ∧
      (nativeCriticalPotentialReactionCLM g hY q z:M→ℝ)=ᵐ[g.volumeMeasure](F:M→ℝ):=by
  let qs:=nativeScaledSmoothBubblePotential e τ a χ
  let U:=toL2 g.leviCivitaData univ z
  have hmSm:MemLp qs ⊤ g.volumeMeasure:=hSm.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp:MemLp (fun y=>nativeScaledFullBubblePotential e K τ a y*U y) 2 g.volumeMeasure:=
    nativeFullBubble_product_memLp_two g e hK τ a U
  have hs:MemLp (fun y=>qs y*U y) 2 g.volumeMeasure:=(Lp.memLp U).mul' hmSm
  have hd:MemLp (fun y=>(nativeScaledFullBubblePotential e K τ a y-qs y)*U y) 2 g.volumeMeasure:=by
    apply (hp.sub hs).ae_eq
    exact Eventually.of_forall fun y=>by simp only [Pi.sub_apply];ring
  have hm:=hd.const_mul 8
  let F:=hm.toLp (fun y=>8*((nativeScaledFullBubblePotential e K τ a y-qs y)*U y))
  have hF:(F:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>8*((nativeScaledFullBubblePotential e K τ a y-qs y)*U y)):=hm.coeFn_toLp
  refine ⟨F,hF,?_⟩
  filter_upwards [nativeCriticalPotentialReactionCLM_ae g hY q z,hq,hF] with y hy hqy hFy
  rw [hy,hqy,hFy]

#print axioms exists_nativeSmoothBubble_same_reaction_L2
end Yamabe3.Analysis.SpherePolar
