import Yamabe3.Analysis.NativeSharedFarTailSolver
import Yamabe3.Analysis.NativeH4UniformCutoffSource
import Yamabe3.Analysis.NativeH4OuterCutoffGeometricWindow

/-! An original-H4 baseline far return from the SHARED receiving
inverse. Only actual critical source senders are used. The receiver
certificate is an explicit intermediate interface, discharged by the
joint actual feedback producer, never asserted to exist by definition. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic Delaunay SphereSpectrum
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Sobolev.Euclidean
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def combinedFarH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] combinedFarH1Normed
private instance combinedFar65:Fact (1 ≤ (6/5:ℝ≥0∞)) := ⟨one_le_sixFifths⟩

theorem exists_nativeH4_far_return_of_shared_receiver
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (P:NativeHighPotential)
    {τ:ℝ} (ht:0 < τ) (L c N:ℝ) (hN:0 ≤ N)
    (hsolver:NativeH4ReceivingTailSolver g e K τ L c N) :
    let S₀:=(exists_nativeH4_uniform_cutoff_source_threshold g gE e he hei hK hKs P ht).choose
    ∀(χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ),
      ∃Ccut:ℝ,0 ≤ Ccut ∧
      ∀s:ℝ,s ≤ S₀ → L ≤ Real.exp (-s-1/2) →
      ∀(n:ℕ) (t:Fin n→ℝ), (∀i,t i ≤ 0) → (∀i,L ≤ Real.exp (-t i-1/2)) →
      ∃Cgeo:ℝ,0 ≤ Cgeo ∧
      ∀(B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
        (hsmall:60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g),
      ∀a:ℝ,0 < a → ball (0:E) (a*L)⊆e.source → (∀i,a*Real.exp (-t i) ≤ 1) →
      let Ω:=e '' ball (0:E) (a*L)
      ∃R:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g B hBs Ω,
        ‖R‖ ≤ N*Real.sqrt a*(Ccut*Real.exp (s/2)+Cgeo*a) ∧
        ∀X:HalfEndPhysicalH4Graph,∀η:H1Zero g.leviCivitaData univ,
            closedYamabeJacobianForm g B hBs (R X).val η=
              ∫y,(nativeDensityCorrectedChartSource gE e K
                (nativePhysicalShellSource a s (nativeCollarCutoffCommutatorCLM χ hχ
                  (nativeH4MatchedExteriorAllScaleJet P ht X s).val)) y+
                (∑i:Fin n,nativeDensityCorrectedChartSource gE e K
                  (nativeH4OuterCutoffGeometricShell gE P ht a s (t i) χ hχ X) y)+
                8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a)) y*
                  toL2 g.leviCivitaData univ (R X).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure := by
  dsimp only
  intro χ hχ
  obtain ⟨D,hD,hcutχ⟩:=(exists_nativeH4_uniform_cutoff_source_threshold g gE e he hei hK hKs P ht).choose_spec.2 χ hχ
  refine ⟨D,hD,?_⟩
  intro s hs hLs n t hts hLt
  obtain ⟨Cgeo,hCgeo,hgeo⟩:=exists_nativeH4Outer_cutoff_geometric_window_source
    g gE hB hρ e he hei hK hKs P ht L s χ hχ n t hts hLt
  refine ⟨Cgeo,hCgeo,?_⟩
  intro B hBs hsmall a ha hsource hr
  let Ω:=e '' ball (0:E) (a*L)
  have hΩ:IsOpen Ω := e.isOpen_image_of_subset_source isOpen_ball hsource
  obtain ⟨Tc,hTc,hTcv⟩:=hcutχ a ha s hs
  obtain ⟨Tg,hTg,hTgv,hTgz⟩:=hgeo a ha hsource hr
  let T:=Tc+Tg
  have hT:‖T‖ ≤ Real.sqrt a*(D*Real.exp (s/2)+Cgeo*a) := by
    apply T.opNorm_le_bound (by positivity)
    intro X
    change ‖Tc X+Tg X‖ ≤ _
    apply (norm_add_le _ _).trans
    apply (add_le_add (Tc.le_of_opNorm_le hTc X) (Tg.le_of_opNorm_le hTg X)).trans_eq
    change D*Real.sqrt a*Real.exp (s/2)*‖X‖+Cgeo*a*Real.sqrt a*‖X‖=_
    change _=Real.sqrt a*(D*Real.exp (s/2)+Cgeo*a)*‖X‖
    ring
  have hTcz (X:HalfEndPhysicalH4Graph):(Tc X:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]0 := by
    filter_upwards [ae_restrict_of_ae (s:=Ω) (hTcv X).2,ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
    rw [hy]
    apply nativeDensityCorrectedChartSource_zero_on_image gE e K (ball (0:E) (a*L)) hsource _ _ y hyΩ
    intro x hx
    exact nativePhysicalShellSource_zero_inner ha s _ hLs (ball_subset_closedBall hx)
  have hTz (X:HalfEndPhysicalH4Graph):(T X:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]0 := by
    filter_upwards [ae_restrict_of_ae (s:=Ω) (Lp.coeFn_add (Tc X) (Tg X)),hTcz X,hTgz X] with y hy hc hg
    change (Tc X+Tg X:Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure) y=0
    rw [hy]
    change Tc X y+Tg X y=0
    rw [hc,hg]
    simp only [Pi.zero_apply,add_zero]
  obtain ⟨R,hR,hRw⟩:=hsolver B hBs hsmall a ha hsource T hTz
  refine ⟨R,(hR.trans (mul_le_mul_of_nonneg_left hT hN)).trans_eq (by ring),?_⟩
  intro X
  intro η
  apply (hRw X η).trans
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add (Tc X) (Tg X),(hTcv X).2,hTgv X] with y hadd htc htg
  change ((Tc X+Tg X:Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure) y+_)*_=_
  rw [hadd]
  change (Tc X y+Tg X y+_)*_=_
  rw [htc,htg]


#print axioms exists_nativeH4_far_return_of_shared_receiver
end Yamabe3.Analysis.SpherePolar
