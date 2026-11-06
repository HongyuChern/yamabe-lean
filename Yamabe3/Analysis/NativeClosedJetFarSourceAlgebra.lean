import Yamabe3.Analysis.NativeDensitySourceAlgebra
import Yamabe3.Analysis.NativeFixedFarL2Source

/-! Exact native far-source algebra on the SAME completion elements.
The actual L2 pairings justify integral addition. Tail reaction and all
raw shell sources are preserved; no prescribed PDE is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

 def nativeClosedJetFarSource
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M) (K:Set E)
    (a S:ℝ) {n:ℕ} (t:Fin n→ℝ) (C:NativeCollarL2) (G:Fin n→NativeCollarL2)
    (q:M→ℝ) (u:H1Zero g.leviCivitaData univ):M→ℝ:=fun y=>
      nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a S C) y+
      (∑i:Fin n,nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a (t i) (G i)) y)+
      8*(q y*toL2 g.leviCivitaData univ u y)

 theorem nativeClosedJetFarSource_add_ae
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:MeasurableSet K) (a S:ℝ) {n:ℕ} (t:Fin n→ℝ)
    (C₀ C₁:NativeCollarL2) (G₀ G₁:Fin n→NativeCollarL2)
    (q:M→ℝ) (u₀ u₁:H1Zero g.leviCivitaData univ):
    nativeClosedJetFarSource g gE e K a S t (C₀+C₁) (G₀+G₁) q (u₀+u₁)=ᵐ[g.volumeMeasure]
      (nativeClosedJetFarSource g gE e K a S t C₀ G₀ q u₀+
        nativeClosedJetFarSource g gE e K a S t C₁ G₁ q u₁):=by
  have hc:=nativeDensityPhysicalShell_add_ae g gE e he hei hK a S C₀ C₁
  have hg(i:Fin n):=nativeDensityPhysicalShell_add_ae g gE e he hei hK a (t i) (G₀ i) (G₁ i)
  have hu:=Lp.coeFn_add (toL2 g.leviCivitaData univ u₀) (toL2 g.leviCivitaData univ u₁)
  rw [←map_add] at hu
  filter_upwards [hc,eventually_all.mpr hg,hu] with y hcy hgy huy
  simp only [nativeClosedJetFarSource,Pi.add_apply]
  rw [hcy,huy]
  simp only [Pi.add_apply] at hgy ⊢
  simp_rw [hgy]
  rw [Finset.sum_add_distrib]
  ring

 theorem nativeClosedJetFarSource_memLp_two
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (a S:ℝ) {n:ℕ} (t:Fin n→ℝ) (C:NativeCollarL2) (G:Fin n→NativeCollarL2)
    (τ c:ℝ) (u:H1Zero g.leviCivitaData univ):
    MemLp (nativeClosedJetFarSource g gE e K a S t C G
      (nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a))) u) 2 g.volumeMeasure:=by
  exact nativeFarSource_sum_memLp_two g gE e he hei hK hKs _
    (nativePhysicalShellSource_memLp_two a S C) n a t G τ c (toL2 g.leviCivitaData univ u)

section
variable [CompactSpace M] [ConnectedSpace M]
private def nativeClosedSourceH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] nativeClosedSourceH1Normed

 theorem nativeWholeWeakSource_equation_add
    (g:RiemannianMetric 3 M) (u₀ u₁:H1Zero g.leviCivitaData univ)
    (f₀ f₁:M→ℝ) (h₀:MemLp f₀ 2 g.volumeMeasure) (h₁:MemLp f₁ 2 g.volumeMeasure)
    (hw₀:∀η:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const u₀ η=
      ∫y,f₀ y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)
    (hw₁:∀η:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const u₁ η=
      ∫y,f₁ y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure):
    ∀η:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (u₀+u₁) η=
      ∫y,(f₀ y+f₁ y)*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure:=by
  intro η
  rw [map_add,ContinuousLinearMap.add_apply,hw₀,hw₁]
  simp_rw [add_mul]
  exact (integral_add (h₀.integrable_mul (Lp.memLp _)) (h₁.integrable_mul (Lp.memLp _))).symm
end

#print axioms nativeClosedJetFarSource_add_ae
#print axioms nativeClosedJetFarSource_memLp_two
#print axioms nativeWholeWeakSource_equation_add
end Yamabe3.Analysis.SpherePolar
