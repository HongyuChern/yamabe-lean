import Yamabe3.Analysis.NativeH4FlatSourceIdentity
import Yamabe3.Analysis.NativeWeakFlatLocality

/-! The cancelled residual is the difference of the actual native weak
operator of one corrected field and the actual flat operator of the
original graph field. Dilation and shell restrictions preserve the
volume a.e. identities; no boundary restriction of such identities is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
def nativeH4ValueCorrectedJet (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v₀:ℝ→ℝ) (hv:Continuous v₀) (hb:∀t,0≤v₀ t ∧ v₀ t≤1)
    (τ:ℝ) (x:HalfEndPhysicalH4Graph) (Y:NativeTwoSidedSource) (i:HalfEndPhysicalSliceIndex):nativeCollarJetClosure:=
  nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i x+
    nativeTwoSidedAllScaleJetCLM P hp v₀ hv hb τ i.val Y

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (p : DelaunayPhaseData κ)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ) (τ : ℝ)
local notation "P" => p.nativeHighPotential hκ0 hκ1
local notation "v₀" => (fun t => p.orbit (t+p.phase))
local notation "hv" => (p.smooth.continuous.comp (continuous_id.add continuous_const))
local notation "hb" => (fun t => p.bounded (t+p.phase))

 theorem nativeH4ValueResidual_row_difference (g : RiemannianMetric 3 E) (ε : ℝ)
    (x : HalfEndPhysicalH4Graph) (Y : NativeTwoSidedSource) (n : ℕ) :
    let s := nativeLogShellCenter n
    let i := nativeH4NonnegativeScaleIndex s (nativeLogShellCenter_nonneg n)
    (nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) g ε x Y n : E→ℝ)=ᵐ[volume.restrict nativeSourceShell]
      (fun y => (nativeOrbitCollarJacobianCLM g (ε*Real.exp (-s)) p.orbit p.smooth p.bounded (p.phase+s)
          (nativeH4ValueCorrectedJet P hp v₀ hv hb τ x Y i).val : E→ℝ) y-
        (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s p.potential) (nativeH4GraphScaleJetCLM i x).val : E→ℝ) y) := by
  let s := nativeLogShellCenter n
  let i := nativeH4NonnegativeScaleIndex s (nativeLogShellCenter_nonneg n)
  let V := boundedTimeTranslate ℝ s p.potential
  let J := nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i x
  let L := nativeTwoSidedAllScaleJetCLM P hp v₀ hv hb τ s Y
  let A := nativeH4GraphScaleJetCLM i x
  let N := nativeOrbitCollarJacobianCLM g (ε*Real.exp (-s)) p.orbit p.smooth p.bounded (p.phase+s)
  have hN : nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g (ε*Real.exp (-s)) V=N := by
    dsimp only [V]
    rw [delaunayPhasePotential_time_translate,nativeBCFCollarError_delaunay_eq]
    rfl
  have hrow : nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) g ε x Y n=N (J.val+L.val)-nativeFlatCollarJetCLM V J.val := by
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

theorem nativeH4ValueResidual_same_physical_operators (g : RiemannianMetric 3 E) (ε : ℝ)
    (x : HalfEndPhysicalH4Graph) (Y : NativeTwoSidedSource)
    (F u : E→ℝ)
    (hF : EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue x)) F (Metric.closedBall (0:E) 4))
    (hu : ∀i : HalfEndPhysicalSliceIndex,
      ((nativeH4ValueCorrectedJet P hp v₀ hv hb τ x Y i).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun y => Real.exp (3*i.1/2)*u (Real.exp (-i.1) • y))) :
    nativePhysicalShellAssembly (nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) g ε x Y)
      =ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})]
      (fun y => nativePhysicalWeakJacobian g ε p.orbit p.phase u y-
        nativePhysicalWeakFlatJacobian p.orbit p.phase F y) := by
  rw [←nativePhysicalShell_union,ae_eq_restrict_iUnion_iff]
  intro n
  let s := nativeLogShellCenter n
  let i := nativeH4NonnegativeScaleIndex s (nativeLogShellCenter_nonneg n)
  have hr := nativeH4ValueResidual_row_difference hκ0 hκ1 p hp τ g ε x Y n
  have hd := ae_comp_dilation (Real.exp_ne_zero s) hr
  change (fun y => (nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) g ε x Y n : E→ℝ) (Real.exp s • y))
      =ᵐ[volume.restrict ((fun y : E => Real.exp s • y) ⁻¹' nativeSourceShell)] _ at hd
  rw [←nativePhysicalShell_dilation n] at hd
  have hn := nativeScaledJet_physical_operator g ε p.orbit p.smooth p.bounded p.phase s
    (nativeH4ValueCorrectedJet P hp v₀ hv hb τ x Y i) (hu i)
  have hf := nativeScaledJet_flat_physical_operator p.orbit p.smooth.continuous p.bounded p.phase s
    (nativeH4GraphScaleJetCLM i x) (nativeH4GraphScaleJet_same_function i x F hF)
  rw [←delaunayPhasePotential_time_translate p s] at hf
  have hn' := ae_mono (Measure.restrict_mono (nativePhysicalShell_subset_window n) le_rfl) hn
  have hf' := ae_mono (Measure.restrict_mono (nativePhysicalShell_subset_window n) le_rfl) hf
  filter_upwards [hd,hn',hf',ae_restrict_mem (nativePhysicalShell_measurable n)] with y hd hn' hf' hy
  rw [nativePhysicalShellAssembly_on _ n hy,nativePhysicalWeakJacobian_on g ε p.orbit p.phase u n hy,
    nativePhysicalWeakFlatJacobian_on p.orbit p.phase F n hy]
  change Real.exp (s/2)*_=_
  rw [hd,mul_sub,hn',hf']
  rfl


#print axioms nativeH4ValueResidual_row_difference
#print axioms nativeH4ValueResidual_same_physical_operators
end Yamabe3.Analysis.UniformElliptic
