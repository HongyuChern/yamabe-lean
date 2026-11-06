import Yamabe3.Analysis.NativeH4OuterCutoffGeometricSender
import Yamabe3.Analysis.NativePhysicalShellSupport
import Yamabe3.Analysis.NativeOuterGeometricHomogeneousSender

/-! The finite far geometric source is built from the SAME original-H4 outer cutoff
product and summed before the small scale is chosen. It is zero on the
fixed receiving ball, ready for one common tail-absorbed solve. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay SphereSpectrum
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private instance cutoffWindow65:Fact (1 ≤ (6/5:ℝ≥0∞)) := ⟨one_le_sixFifths⟩

def nativeH4OuterCutoffGeometricShell (gE:RiemannianMetric 3 E)
    (P:NativeHighPotential)
    {τ:ℝ} (ht:0 < τ)
    (a S s:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (X:HalfEndPhysicalH4Graph) : E→ℝ :=
  nativePhysicalShellSource a s
    (nativeBCFCollarErrorCLM gE (a*Real.exp (-s))
      (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
      (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S s χ)
        (nativeOuterFieldCutoffAtScale_smooth S s hχ)
        (nativeH4MatchedExteriorAllScaleJet P ht X s)).val)

theorem exists_nativeH4Outer_cutoff_geometric_window_source
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (P:NativeHighPotential)
    {τ:ℝ} (ht:0 < τ)
    (L S:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (n:ℕ) (s:Fin n→ℝ)
    (hs:∀i,s i ≤ 0) (hLs:∀i,L ≤ Real.exp (-s i-1/2)) :
    ∃C:ℝ,0 ≤ C ∧ ∀a:ℝ,0 < a → ball (0:E) (a*L)⊆e.source → (∀i,a*Real.exp (-s i) ≤ 1) →
      ∃T:HalfEndPhysicalH4Graph →L[ℝ] Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure,
        ‖T‖ ≤ C*a*Real.sqrt a ∧
        (∀X,(T X:M→ℝ)=ᵐ[g.volumeMeasure]
          fun y=>∑i:Fin n,nativeDensityCorrectedChartSource gE e K
            (nativeH4OuterCutoffGeometricShell gE P ht a S (s i) χ hχ X) y) ∧
        ∀X,(T X:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' ball (0:E) (a*L))]0 := by
  obtain ⟨D,hD,hsa⟩:=exists_nativeH4Outer_cutoff_geometric_sender g gE hB hρ e he hei hK hKs P ht
  let Mχ i:=nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (s i) χ)
    (nativeOuterFieldCutoffAtScale_smooth S (s i) hχ)
  let C:=D*∑i:Fin n,‖Mχ i‖*Real.exp (-3*s i)
  have hC:0 ≤ C := by dsimp only [C];positivity
  refine ⟨C,hC,fun a ha hsource hr=>?_⟩
  let Q (i:Fin n):HalfEndPhysicalH4Graph →L[ℝ] Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure :=
    (hsa a ha (s i) (hs i) (hr i) S χ hχ).choose
  have hQ i:‖Q i‖ ≤ D*‖Mχ i‖*a*Real.sqrt a*Real.exp (-3*s i) :=
    (hsa a ha (s i) (hs i) (hr i) S χ hχ).choose_spec.1
  have hQv i X:(Q i X:M→ℝ)=ᵐ[g.volumeMeasure]
      nativeDensityCorrectedChartSource gE e K (nativeH4OuterCutoffGeometricShell gE P ht a S (s i) χ hχ X) :=
    (hsa a ha (s i) (hs i) (hr i) S χ hχ).choose_spec.2 X |>.2
  let T:=∑i:Fin n,Q i
  have hT:‖T‖ ≤ C*a*Real.sqrt a := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i _=>hQ i)).trans_eq
    dsimp only [C]
    rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hTv X:(T X:M→ℝ)=ᵐ[g.volumeMeasure]
      fun y=>∑i:Fin n,nativeDensityCorrectedChartSource gE e K
        (nativeH4OuterCutoffGeometricShell gE P ht a S (s i) χ hχ X) y := by
    have hf:=Lp.coeFn_fun_finsetSum Finset.univ (fun i:Fin n=>Q i X)
    have he:T X=∑i:Fin n,Q i X := by simp only [T,ContinuousLinearMap.sum_apply]
    rw [he]
    apply hf.trans
    filter_upwards [ae_all_iff.mpr (fun i=>hQv i X)] with y hy
    exact Finset.sum_congr rfl (fun i _=>hy i)
  have hΩ:IsOpen (e '' ball (0:E) (a*L)) := e.isOpen_image_of_subset_source isOpen_ball hsource
  refine ⟨T,hT,hTv,?_⟩
  intro X
  filter_upwards [ae_restrict_of_ae (s:=e '' ball (0:E) (a*L)) (hTv X),ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
  rw [hy]
  apply Finset.sum_eq_zero
  intro i _
  apply nativeDensityCorrectedChartSource_zero_on_image gE e K (ball (0:E) (a*L)) hsource _ _ y hyΩ
  intro x hx
  exact nativePhysicalShellSource_zero_inner ha (s i) _ (hLs i) (ball_subset_closedBall hx)

#print axioms exists_nativeH4Outer_cutoff_geometric_window_source
end Yamabe3.Analysis.SpherePolar
