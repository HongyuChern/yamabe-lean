import Yamabe3.Analysis.NativeH4PhysicalResidual
import Yamabe3.Analysis.NativeScaledJetOperator

/-! The coupled Poisson term preserves the original model source on
the positive region. Hence the cancelled residual is the actual native
operator of the corrected field minus the original graph field's flat
operator, on every physical source shell. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay

 theorem nativeH4Matched_flat_preserves_source (B P : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (i : HalfEndPhysicalSliceIndex) (x : HalfEndPhysicalH4Graph) :
    nativePositiveScaledRestrictionCLM i.1 (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ i.1 P.potential)
      (nativeH4MatchedScaleJetCLM B P hp i x).val)=
      nativePositiveScaledRestrictionCLM i.1 (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ i.1 P.potential)
        (nativeH4GraphScaleJetCLM i x).val) := by
  let J := nativeBoundaryPoissonJetCLM P hp (nativeH4GraphSigmaCLM B P)
    (nativeH4GraphSigma_regular B P) (nativeH4GraphSigma_energy_bound B P) i.1 x
  let V := boundedTimeTranslate ℝ i.1 P.potential
  have hz : nativePositiveScaledRestrictionCLM i.1 (nativeFlatCollarJetCLM V J.val)=0 := by
    change nativePositiveScaledRestrictionCLM i.1
      (-((∑j : Fin 3,nativePoissonAllScaleSecond P hp i.1 (nativeH4GraphSigmaCLM B P x) j j)+
        nativeCollarPotentialMulCLM V (nativePoissonAllScaleValue P hp i.1 (nativeH4GraphSigmaCLM B P x))))=0
    rw [map_neg,nativePoissonAllScale_homogeneous P hp i.1 _ (nativeH4GraphSigma_regular B P x),neg_zero]
  change nativePositiveScaledRestrictionCLM i.1 (nativeFlatCollarJetCLM V ((nativeH4GraphScaleJetCLM i x).val+J.val))=_
  rw [map_add,map_add,hz,add_zero]

 theorem nativePositiveScaled_equal_shell_ae (n : ℕ) (U W : NativeCollarL2)
    (he : nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) U=
      nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) W) :
    (U : E→ℝ)=ᵐ[volume.restrict nativeSourceShell] (W : E→ℝ) := by
  let D := nativePositiveScaledCollar (nativeLogShellCenter n)
  have hμ : volume.restrict D≤volume.restrict nativePoissonEntranceCollar := Measure.restrict_mono inter_subset_left le_rfl
  have hU : (nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) U : E→ℝ)=ᵐ[volume.restrict D] (U : E→ℝ) :=
    l2MeasureRestrict_ae hμ U
  have hW : (nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) W : E→ℝ)=ᵐ[volume.restrict D] (W : E→ℝ) :=
    l2MeasureRestrict_ae hμ W
  rw [he] at hU
  exact ae_mono (Measure.restrict_mono (nativeSourceShell_subset_positiveScale n) le_rfl) (hU.symm.trans hW)

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (p : DelaunayPhaseData κ)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ) (τ : ℝ)
local notation "P" => p.nativeHighPotential hκ0 hκ1
local notation "v₀" => (fun t => p.orbit (t+p.phase))
local notation "hv" => (p.smooth.continuous.comp (continuous_id.add continuous_const))
local notation "hb" => (fun t => p.bounded (t+p.phase))

 theorem nativeH4Residual_row_difference (g : RiemannianMetric 3 E) (ε : ℝ)
    (T : HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource) (x : HalfEndPhysicalH4Graph) (n : ℕ) :
    let s := nativeLogShellCenter n
    let i := nativeH4NonnegativeScaleIndex s (nativeLogShellCenter_nonneg n)
    (nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) g ε x (T x) n : E→ℝ)=ᵐ[volume.restrict nativeSourceShell]
      (fun y => (nativeOrbitCollarJacobianCLM g (ε*Real.exp (-s)) p.orbit p.smooth p.bounded (p.phase+s)
          (nativeH4CorrectedScaleJetCLM P hp v₀ hv hb (τ:=τ) T i x).val : E→ℝ) y-
        (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s p.potential) (nativeH4GraphScaleJetCLM i x).val : E→ℝ) y) := by
  let s := nativeLogShellCenter n
  let i := nativeH4NonnegativeScaleIndex s (nativeLogShellCenter_nonneg n)
  let V := boundedTimeTranslate ℝ s p.potential
  let J := nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i x
  let L := nativeTwoSidedAllScaleJetCLM P hp v₀ hv hb τ s (T x)
  let A := nativeH4GraphScaleJetCLM i x
  let N := nativeOrbitCollarJacobianCLM g (ε*Real.exp (-s)) p.orbit p.smooth p.bounded (p.phase+s)
  have hN : nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g (ε*Real.exp (-s)) V=N := by
    dsimp only [V]
    rw [delaunayPhasePotential_time_translate,nativeBCFCollarError_delaunay_eq]
    rfl
  have hrow : nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) g ε x (T x) n=N (J.val+L.val)-nativeFlatCollarJetCLM V J.val := by
    change nativeBCFCollarErrorCLM g (ε*Real.exp (-s)) V J.val+
      (nativeFlatCollarJetCLM V L.val+nativeBCFCollarErrorCLM g (ε*Real.exp (-s)) V L.val)=_
    rw [←hN]
    simp only [ContinuousLinearMap.add_apply,map_add]
    abel
  have hbase := nativePositiveScaled_equal_shell_ae n _ _
    (nativeH4Matched_flat_preserves_source (fullBubbleHighPotential (-τ)) P hp i x)
  change (nativeFlatCollarJetCLM V J.val : E→ℝ)=ᵐ[volume.restrict nativeSourceShell]
    (nativeFlatCollarJetCLM V A.val : E→ℝ) at hbase
  dsimp only
  rw [hrow]
  have hs := ae_mono (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl)
    (Lp.coeFn_sub (N (J.val+L.val)) (nativeFlatCollarJetCLM V J.val))
  filter_upwards [hbase,hs] with y hbasey hsuby
  rw [hsuby]
  change N (J.val+L.val) y-nativeFlatCollarJetCLM V J.val y=N (J.val+L.val) y-nativeFlatCollarJetCLM V A.val y
  rw [hbasey]

#print axioms nativeH4Matched_flat_preserves_source
#print axioms nativePositiveScaled_equal_shell_ae
#print axioms nativeH4Residual_row_difference
end Yamabe3.Analysis.UniformElliptic
