import Yamabe3.Analysis.NativeEnergyReceiverScaling
import Yamabe3.Analysis.WeakLaplacianDilation
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.L2Pullback

/-! Native local AE identity survives the compact chart and nonzero
volume dilation. The L2 return estimate therefore concerns the same
smooth representative, not an unrelated L6 realisation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeChart_scaled_local_ae
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {Ω:Set M} (hΩ:MeasurableSet Ω) {U V:M→ℝ}
    (hUV:U=ᵐ[g.volumeMeasure.restrict Ω]V)
    (O:Set E) (hO:MeasurableSet O) (t:ℝ)
    (hmap:MapsTo (fun x:E=>Real.exp t • x) O K)
    (hmapΩ:∀x∈O,e (Real.exp t • x)∈Ω) :
    (fun x:E=>U (e (Real.exp t • x)))=ᵐ[volume.restrict O]
      (fun x:E=>V (e (Real.exp t • x))) := by
  have hglobal:Ω.indicator U=ᵐ[g.volumeMeasure]Ω.indicator V:=by
    have hh:=(ae_restrict_iff' hΩ).mp hUV
    filter_upwards [hh] with y hy
    by_cases h:y∈Ω
    · rw [indicator_of_mem h,indicator_of_mem h,hy h]
    · rw [indicator_of_notMem h,indicator_of_notMem h]
  have hc:=g.ae_comp_on_compact e he hei hK hKs hglobal
  have hd:=ae_comp_dilation (Real.exp_pos t).ne' hc
  filter_upwards [ae_mono (Measure.restrict_mono hmap le_rfl) hd,ae_restrict_mem hO] with x hx ho
  simpa only [indicator_of_mem (hmapΩ x ho)] using hx

variable [CompactSpace M] [ConnectedSpace M]
private def reprReceiverH1Normed (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] reprReceiverH1Normed

theorem exists_nativeRepresentative_rescaled_receiver_L2_bound
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (O:Set E) (hO:MeasurableSet O) (hvol:volume O<⊤) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀(W:H1Zero g.leviCivitaData univ) (t:ℝ),
      MapsTo (fun x:E=>Real.exp t • x) O K→
      ∀(Ω:Set M),MeasurableSet Ω→∀U:M→ℝ,
      U=ᵐ[g.volumeMeasure.restrict Ω](toL2 g.leviCivitaData univ W:M→ℝ)→
      (∀x∈O,e (Real.exp t • x)∈Ω)→
      MemLp (fun x:E=>U (e (Real.exp t • x))) 2 (volume.restrict O) ∧
      eLpNorm (fun x:E=>U (e (Real.exp t • x))) 2 (volume.restrict O)≤
        C*ENNReal.ofReal (Real.exp (-t/2))*ENNReal.ofReal ‖W‖ := by
  obtain ⟨C,hC,hb⟩:=exists_nativeEnergy_rescaled_receiver_L2_bound g hY e he hei hK hKs O hO hvol
  refine ⟨C,hC,fun W t hmap Ω hΩ U hU hmapΩ=>?_⟩
  have hh:=hb W t hmap
  have hAE:U=ᵐ[g.volumeMeasure.restrict Ω](GreenMass.NativeEnergyL6.toL6 g hY W:M→ℝ):=
    hU.trans (ae_restrict_of_ae (GreenMass.NativeEnergyL6.toL6_ae_toL2 g hY W).symm)
  have heq:=nativeChart_scaled_local_ae g e he hei hK hKs hΩ hAE O hO t hmap hmapΩ
  exact ⟨hh.1.ae_eq heq.symm,(eLpNorm_congr_ae heq).le.trans hh.2⟩

#print axioms nativeChart_scaled_local_ae
#print axioms exists_nativeRepresentative_rescaled_receiver_L2_bound
end Yamabe3.Analysis.SpherePolar
