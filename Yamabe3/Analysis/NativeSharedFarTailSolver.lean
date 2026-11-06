import Yamabe3.Analysis.NativeCombinedFarTailSolver
import Yamabe3.Analysis.NativeOuterCutoffGeometricWindowSource

/-! The SAME tail cutoff and native inverse serve the supported-L2
feedback and arbitrary actual H4-baseline critical sources. The generic
receiver is exposed here because separately chosen inverses do not
establish a coherent original-source assembly. -/
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

def NativeH4ReceivingTailSolver
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M) (K:Set E)
    (τ L c N:ℝ) : Prop :=
  ∀(B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (hsmall:60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g),
  ∀a:ℝ,0 < a → ball (0:E) (a*L)⊆e.source →
  let Ω:=e '' ball (0:E) (a*L)
  ∀T:HalfEndPhysicalH4Graph →L[ℝ] Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure,
    (∀x:HalfEndPhysicalH4Graph,(T x:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]0) →
    ∃R:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g B hBs Ω,
      ‖R‖ ≤ N*‖T‖ ∧ ∀x:HalfEndPhysicalH4Graph,∀η:H1Zero g.leviCivitaData univ,
        closedYamabeJacobianForm g B hBs (R x).val η=
          ∫y,(T x y+8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a)) y*
            toL2 g.leviCivitaData univ (R x).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure

theorem exists_nativeCombined_far_tail_solver_with_original_receiver
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) {τ:ℝ} (ht:0 < τ)
    (L:ℝ) (hL:0 < L) :
    ∃c N:ℝ,Real.log (max 128 L) ≤ c ∧ 0 < N ∧
      NativeH4ReceivingTailSolver g e K τ L c N ∧
      ∀(b:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ),
      (∀x:E,x∉nativeSourceShell → ∀i:Fin 3,
        partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0) →
      ∃S₀ Ccut:ℝ,S₀ ≤ -(1/2:ℝ) ∧ 0 ≤ Ccut ∧
      ∀s:ℝ,s ≤ S₀ → L ≤ Real.exp (-s-1/2) →
      ∀(n:ℕ) (t:Fin n→ℝ), (∀i,t i ≤ 0) → (∀i,L ≤ Real.exp (-t i-1/2)) →
      ∃Cgeo:ℝ,0 ≤ Cgeo ∧
      ∀(B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
        (hsmall:60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g),
      ∀a:ℝ,0 < a → ball (0:E) (a*L)⊆e.source → (∀i,a*Real.exp (-t i) ≤ 1) →
      let Ω:=e '' ball (0:E) (a*L)
      ∃R:nativeSupportedSourcePairSpace b →L[ℝ] nativeHomogeneousEnergySpace g B hBs Ω,
        ‖R‖ ≤ N*Real.sqrt a*(Ccut*Real.exp (s/2)+Cgeo*a) ∧
        ∀X:nativeSupportedSourcePairSpace b,∃w:ℝ×SpherePolar.S→ℝ,Measurable w ∧
          (∀r,(fun θ=>w (r,θ))=ᵐ[angularVolume]
            (nativeSupportedOuterCurve b ht X.val.2
              (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
              (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val) r:SpherePolar.S→ℝ)) ∧
          ∀η:H1Zero g.leviCivitaData univ,
            closedYamabeJacobianForm g B hBs (R X).val η=
              ∫y,(nativeDensityCorrectedChartSource gE e K
                (physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation s (cylinderLift w)) s a) y+
                (∑i:Fin n,nativeDensityCorrectedChartSource gE e K
                  (nativeOuterCutoffGeometricShell gE P hp v hv hb b ht a s (t i) χ hχ X.val) y)+
                8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a)) y*
                  toL2 g.leviCivitaData univ (R X).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure := by
  obtain ⟨c,N,hc,hN,hsolver⟩:=exists_nativeReceiving_tail_solver g hY e he hei hK hKs τ L hL
  refine ⟨c,N,hc,hN,?_,?_⟩
  · intro B hBs hsmall a ha hsource
    dsimp only
    intro T hz
    exact hsolver B hBs hsmall a ha hsource HalfEndPhysicalH4Graph T hz
  · intro b χ hχ hχs
    obtain ⟨Sc,D,hSc,hD,hcut⟩:=exists_nativeSupported_cutoff_source_CLM g gE e he hei hK hKs P hp v hv hb b ht χ hχ
    obtain ⟨Sf,hSf,J,hJ,hfield⟩:=exists_nativeSupportedOuter_same_field_Newton_annulus_H4 b ht
    refine ⟨min Sc Sf,D,(min_le_left _ _).trans hSc,hD,?_⟩
    intro s hs hLs n t hts hLt
    obtain ⟨Cgeo,hCgeo,hgeo⟩:=exists_nativeOuter_cutoff_geometric_window_source
      g gE hB hρ e he hei hK hKs P hp v hv hb b ht L s χ hχ n t hts hLt
    refine ⟨Cgeo,hCgeo,?_⟩
    intro B hBs hsmall a ha hsource hr
    dsimp only
    let Ω:=e '' ball (0:E) (a*L)
    have hΩ:IsOpen Ω := e.isOpen_image_of_subset_source isOpen_ball hsource
    obtain ⟨Tc,hTc,hTcv⟩:=hcut a ha s (hs.trans (min_le_left _ _))
    obtain ⟨Tg,hTg,hTgv,hTgz⟩:=hgeo a ha hsource hr
    let I:=(nativeSupportedSourcePairSpace b).subtypeL
    let T:=Tc+Tg.comp I
    have hT:‖T‖ ≤ Real.sqrt a*(D*Real.exp (s/2)+Cgeo*a) := by
      apply T.opNorm_le_bound (by positivity)
      intro X
      change ‖Tc X+Tg X.val‖ ≤ _
      apply (norm_add_le _ _).trans
      apply (add_le_add (Tc.le_of_opNorm_le hTc X) (Tg.le_of_opNorm_le hTg X.val)).trans_eq
      change D*Real.sqrt a*Real.exp (s/2)*‖X.val‖+Cgeo*a*Real.sqrt a*‖X.val‖=_
      change _=Real.sqrt a*(D*Real.exp (s/2)+Cgeo*a)*‖X.val‖
      ring
    have hTcz (X:nativeSupportedSourcePairSpace b):(Tc X:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]0 := by
      filter_upwards [ae_restrict_of_ae (s:=Ω) (hTcv X).2,ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
      rw [hy]
      apply nativeDensityCorrectedChartSource_zero_on_image gE e K (ball (0:E) (a*L)) hsource _ _ y hyΩ
      intro x hx
      exact nativePhysicalShellSource_zero_inner ha s _ hLs (ball_subset_closedBall hx)
    have hTz (X:nativeSupportedSourcePairSpace b):(T X:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]0 := by
      filter_upwards [ae_restrict_of_ae (s:=Ω) (Lp.coeFn_add (Tc X) (Tg X.val)),hTcz X,hTgz X.val] with y hy hc hg
      change (Tc X+Tg X.val:Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure) y=0
      rw [hy]
      change Tc X y+Tg X.val y=0
      rw [hc,hg]
      simp only [Pi.zero_apply,add_zero]
    obtain ⟨R,hR,hRw⟩:=hsolver B hBs hsmall a ha hsource (nativeSupportedSourcePairSpace b) T hTz
    refine ⟨R,(hR.trans (mul_le_mul_of_nonneg_left hT hN.le)).trans_eq (by ring),?_⟩
    intro X
    have hF:∀ᵐr:ℝ∂volume,r < b → X.val.2 r=0 :=
      (nativeSupportedSourcePairSpace_mem_iff b X.val).mp X.property
    obtain ⟨w,hw,hl,hae,hjet,hreg⟩:=hfield X.val.2
      (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
      (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val)
      (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X.val) hF
    refine ⟨w,hw,hae,?_⟩
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
    filter_upwards [Lp.coeFn_add (Tc X) (Tg X.val),(hTcv X).2,hTgv X.val,hnative] with y hadd htc htg hnat
    change ((Tc X+Tg X.val:Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure) y+_)*_=_
    rw [hadd]
    change (Tc X y+Tg X.val y+_)*_=_
    rw [htc,htg]
    simp only [nativeDensityCorrectedChartSource]
    rw [hnat]

#print axioms exists_nativeCombined_far_tail_solver_with_original_receiver
end Yamabe3.Analysis.SpherePolar
