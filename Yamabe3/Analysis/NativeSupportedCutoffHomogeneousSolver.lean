import Yamabe3.Analysis.NativeSupportedCutoffSourceCLM
import Yamabe3.Analysis.NativePhysicalCutoffSourceIdentity
import Yamabe3.Analysis.NativeOuterGeometricHomogeneousSender

/-! A real far-cutoff solver on the COMPLETE supported source-pair space.
Its output is one bounded linear native H1 field, homogeneous on the
fixed receiving ball, solving the WHOLE cutoff source of the SAME outer
field, plus the actual absorbed bubble tail. The Newton gain is explicit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic Delaunay SphereSpectrum
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Sobolev.Euclidean
private def cutoffHomogeneousH1Normed {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] cutoffHomogeneousH1Normed
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem exists_nativeSupported_cutoff_homogeneous_solver
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)
    (L:ℝ) (hL:0 < L) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (hχs:∀x:E,x∉nativeSourceShell → ∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0) :
    ∃c S C:ℝ,Real.log (max 128 L) ≤ c ∧ S ≤ -(1/2:ℝ) ∧ 0 ≤ C ∧
      ∀(B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
        (hsmall:60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g),
      ∀a:ℝ,0 < a → ball (0:E) (a*L)⊆e.source →
      ∀s:ℝ,s ≤ S → L ≤ Real.exp (-s-1/2) →
      let Ω:=e '' ball (0:E) (a*L)
      ∃R:nativeSupportedSourcePairSpace b →L[ℝ] nativeHomogeneousEnergySpace g B hBs Ω,
        ‖R‖ ≤ C*Real.sqrt a*Real.exp (s/2) ∧ ∀X:nativeSupportedSourcePairSpace b,
        ∃w:ℝ×SpherePolar.S→ℝ,Measurable w ∧
          (∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume]
            (nativeSupportedOuterCurve b ht X.val.2
              (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
              (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val) t:SpherePolar.S→ℝ)) ∧
          (∀t:ℝ,NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht X.val.2
              (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
              (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val)
              (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X.val) t) t w) ∧
          ∀η:H1Zero g.leviCivitaData univ,
            closedYamabeJacobianForm g B hBs (R X).val η=
              ∫y,(nativeDensityCorrectedChartSource gE e K
                (physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation s (cylinderLift w)) s a) y+
                8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a)) y*
                  toL2 g.leviCivitaData univ (R X).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure := by
  obtain ⟨c,N,hc,hN,hsolver⟩:=exists_nativeReceiving_tail_solver g hY e he hei hK hKs τ L hL
  obtain ⟨S0,D,hS0,hD,hsender⟩:=exists_nativeSupported_cutoff_source_CLM g gE e he hei hK hKs P hp v hv hb b ht χ hχ
  obtain ⟨S1,hS1,J,hJ,hfield⟩:=exists_nativeSupportedOuter_same_field_Newton_annulus_H4 b ht
  refine ⟨c,min S0 S1,N*D,hc,(min_le_left _ _).trans hS0,mul_nonneg hN.le hD,?_⟩
  intro B hBs hsmall a ha hsource s hs hLs
  dsimp only
  let Ω:=e '' ball (0:E) (a*L)
  have hΩ:IsOpen Ω := e.isOpen_image_of_subset_source isOpen_ball hsource
  obtain ⟨T,hT,hTv⟩:=hsender a ha s (hs.trans (min_le_left _ _))
  have hzero (X:nativeSupportedSourcePairSpace b):(T X:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]0 := by
    filter_upwards [ae_restrict_of_ae (s:=Ω) (hTv X).2,ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
    rw [hy]
    apply nativeDensityCorrectedChartSource_zero_on_image gE e K (ball (0:E) (a*L)) hsource _ _ y hyΩ
    intro x hx
    exact nativePhysicalShellSource_zero_inner ha s _ hLs (ball_subset_closedBall hx)
  obtain ⟨R,hR,hRw⟩:=hsolver B hBs hsmall a ha hsource (nativeSupportedSourcePairSpace b) T hzero
  refine ⟨R,hR.trans ((mul_le_mul_of_nonneg_left hT hN.le).trans_eq (by ring)),?_⟩
  intro X
  have hF:∀ᵐt:ℝ∂volume,t < b → X.val.2 t=0 :=
    (nativeSupportedSourcePairSpace_mem_iff b X.val).mp X.property
  obtain ⟨w,hw,hl,hae,hjet,hreg⟩:=hfield X.val.2
    (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
    (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val)
    (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X.val) hF
  refine ⟨w,hw,hae,hjet,?_⟩
  intro η
  have hphys:=nativeCollarCutoffCommutator_physical_identity χ hχ hχs
    (nativeSupportedOuterAllScaleJet b ht X.val.2
      (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
      (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val)
      (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X.val) s)
    ((hreg s (hs.trans (min_le_right _ _))).1.le_of_le (by norm_num:1 ≤ 4)) (hjet s) a s
  have hnative:=nativeCompactChart_congr_volume_ae g e he hei hK.measurableSet
    (ae_restrict_of_ae (s:=K) hphys |>.mono (fun y hy=>congrArg (fun z:ℝ=>z/gE.pullbackVolumeDensity id y) hy))
  apply (hRw X η).trans
  apply integral_congr_ae
  filter_upwards [(hTv X).2,hnative] with y hy hn
  rw [hy]
  simp only [nativeDensityCorrectedChartSource]
  rw [hn]

#print axioms exists_nativeSupported_cutoff_homogeneous_solver
end Yamabe3.Analysis.SpherePolar
