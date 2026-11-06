import Yamabe3.Analysis.NativeOuterGeometricPhysicalSender
import Yamabe3.Analysis.NativeReceivingTailSolver
import Yamabe3.Analysis.NativePhysicalShellSupport

/-! The SAME actual outer geometric error is solved globally and returns
to the actual closed homogeneous space on the prescribed receiving ball.
The proof pays all critical/native/tail costs and proves source support. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic Delaunay SphereSpectrum
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def geometricHomogeneousH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] geometricHomogeneousH1Normed

 theorem nativeDensityCorrectedChartSource_zero_on_image
    (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M) (K D:Set E)
    (hD:D⊆e.source) (f:E→ℝ) (hf:∀x∈D,f x=0) :
    ∀y∈e '' D,nativeDensityCorrectedChartSource gE e K f y=0 := by
  rintro y ⟨x,hx,rfl⟩
  rw [nativeDensityCorrectedChartSource,nativeCompactChartFunction,coordinateExtension_comp_apply e _ (hD hx)]
  by_cases hk:x∈K
  · rw [indicator_of_mem hk,hf x hx,zero_div]
  · rw [indicator_of_notMem hk]

theorem exists_nativeOuter_geometric_homogeneous_sender
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)
    (L:ℝ) (hL:0 < L) :
    ∃c C:ℝ,Real.log (max 128 L) ≤ c ∧ 0 ≤ C ∧
      ∀(B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
        (hsmall:60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g),
      ∀a:ℝ,0 < a → ball (0:E) (a*L)⊆e.source →
      ∀s:ℝ,s ≤ 0 → a*Real.exp (-s) ≤ 1 → L ≤ Real.exp (-s-1/2) →
      let Ω:=e '' ball (0:E) (a*L)
      ∃R:NativeTwoSidedSource →L[ℝ] nativeHomogeneousEnergySpace g B hBs Ω,
        ‖R‖ ≤ C*a*Real.sqrt a*Real.exp (-3*s) ∧ ∀X:NativeTwoSidedSource,
          let U:=nativeBCFCollarErrorCLM gE (a*Real.exp (-s))
            (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
            (nativeSupportedOuterAllScaleJet b ht X.2
              (nativeLowL2AngularCLM v hv hb X.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.1)
              (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X)
              (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X) s).val
          ∀η:H1Zero g.leviCivitaData univ,
            closedYamabeJacobianForm g B hBs (R X).val η=
              ∫y,(nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U) y+
                8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a)) y*
                  toL2 g.leviCivitaData univ (R X).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure := by
  obtain ⟨c,N,hc,hN,hsolver⟩:=exists_nativeReceiving_tail_solver g hY e he hei hK hKs τ L hL
  obtain ⟨D,hD,hsender⟩:=exists_nativeOuter_geometric_physical_sender g gE hB hρ e he hei hK hKs P hp v hv hb b ht
  refine ⟨c,N*D,hc,mul_nonneg hN.le hD,?_⟩
  intro B hBs hsmall a ha hsource s hs hr hLs
  dsimp only
  let Ω:=e '' ball (0:E) (a*L)
  have hΩ:IsOpen Ω := e.isOpen_image_of_subset_source isOpen_ball hsource
  obtain ⟨T,hT,hTv⟩:=hsender a ha s hs hr
  have hzero (X:NativeTwoSidedSource):(T X:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]0 := by
    have hh:=ae_restrict_of_ae (s:=Ω) (hTv X).2
    filter_upwards [hh,ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
    rw [hy]
    apply nativeDensityCorrectedChartSource_zero_on_image gE e K (ball (0:E) (a*L)) hsource _ _ y hyΩ
    intro x hx
    exact nativePhysicalShellSource_zero_inner ha s _ hLs (ball_subset_closedBall hx)
  obtain ⟨R,hR,hRw⟩:=hsolver B hBs hsmall a ha hsource NativeTwoSidedSource T hzero
  refine ⟨R,hR.trans ((mul_le_mul_of_nonneg_left hT hN.le).trans_eq (by ring)),?_⟩
  intro X η
  apply (hRw X η).trans
  apply integral_congr_ae
  filter_upwards [(hTv X).2] with y hy
  rw [hy]

#print axioms nativeDensityCorrectedChartSource_zero_on_image
#print axioms exists_nativeOuter_geometric_homogeneous_sender
end Yamabe3.Analysis.SpherePolar
