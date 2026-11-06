import Yamabe3.Analysis.NativeLocalH2ScaledSource
import Yamabe3.Analysis.NativeBubbleTailBoundedL2
import Yamabe3.Analysis.NativeDensityCorrectedChartLp
import Yamabe3.Analysis.NativeForcedEnergyDataMembership

/-! Actual fixed-scale global L2 sources, including the SAME absorbed
native tail. This supplies regularity of the computed source, not its
identification with the prescribed original exterior source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

 theorem nativeBubbleTail_product_memLp_two
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    {K:Set E} (hK:IsCompact K) (τ c t:ℝ) (F:Lp ℝ 2 g.volumeMeasure):
    MemLp (fun y=>nativeCompactChartFunction e K (fullBubbleScaledTail τ c t) y*F y) 2 g.volumeMeasure:=by
  obtain ⟨C,hC,T,hT,hae⟩:=exists_nativeBubbleTail_bounded_L2_multiplier g e hK τ c t
  exact (Lp.memLp (T F)).ae_eq (hae F)

 theorem nativeDensityShell_finite_memLp_two
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (n:ℕ) (a:ℝ) (t:Fin n→ℝ) (U:Fin n→NativeCollarL2):
    MemLp (fun y=>∑i:Fin n,nativeDensityCorrectedChartSource gE e K
      (nativePhysicalShellSource a (t i) (U i)) y) 2 g.volumeMeasure:=by
  obtain ⟨C,hC,hbound⟩:=exists_nativeDensityCorrectedChart_lp_bound g gE e he hei hK hKs 2
  exact memLp_finsetSum Finset.univ (fun i _=>(hbound _ (nativePhysicalShellSource_memLp_two a (t i) (U i))).1)

 theorem nativeFarSource_sum_memLp_two
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (f:E→ℝ) (hf:MemLp f 2 volume) (n:ℕ) (a:ℝ) (t:Fin n→ℝ)
    (U:Fin n→NativeCollarL2) (τ c:ℝ) (R:Lp ℝ 2 g.volumeMeasure):
    MemLp (fun y=>nativeDensityCorrectedChartSource gE e K f y+
      (∑i:Fin n,nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a (t i) (U i)) y)+
      8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a)) y*R y)) 2 g.volumeMeasure:=by
  obtain ⟨C,hC,hbound⟩:=exists_nativeDensityCorrectedChart_lp_bound g gE e he hei hK hKs 2
  exact ((hbound f hf).1.add (nativeDensityShell_finite_memLp_two g gE e he hei hK hKs n a t U)).add
    ((nativeBubbleTail_product_memLp_two g e hK τ c (Real.log a) R).const_mul 8)

section GlobalWeakSource
variable [CompactSpace M] [ConnectedSpace M]
private def nativeFixedSourceH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] nativeFixedSourceH1Normed

 theorem nativeWholeWeakSource_of_memLp
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (W:H1Zero g.leviCivitaData univ) (f:M→ℝ) (hf:MemLp f 2 g.volumeMeasure)
    (hweak:∀η:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g B hB W η=
      ∫y,f y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure):
    ∃F:Lp ℝ 2 g.volumeMeasure,(F:M→ℝ)=ᵐ[g.volumeMeasure]f ∧
      ∀η:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g B hB W η=
        inner ℝ F (toL2 g.leviCivitaData univ η):=by
  let F:=hf.toLp f
  refine ⟨F,hf.coeFn_toLp,fun η=>?_⟩
  rw [hweak,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  simp only [Real.inner_apply]
  rw [hy]

end GlobalWeakSource
#print axioms nativeBubbleTail_product_memLp_two
#print axioms nativeDensityShell_finite_memLp_two
#print axioms nativeFarSource_sum_memLp_two
#print axioms nativeWholeWeakSource_of_memLp
end Yamabe3.Analysis.SpherePolar
