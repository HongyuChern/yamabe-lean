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
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (p : DelaunayPhaseData κ)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ) (τ : ℝ)
local notation "P" => p.nativeHighPotential hκ0 hκ1
local notation "v₀" => (fun t => p.orbit (t+p.phase))
local notation "hv" => (p.smooth.continuous.comp (continuous_id.add continuous_const))
local notation "hb" => (fun t => p.bounded (t+p.phase))

theorem nativeH4Residual_same_physical_operators (g : RiemannianMetric 3 E) (ε : ℝ)
    (T : HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource) (x : HalfEndPhysicalH4Graph)
    (F u : E→ℝ)
    (hF : EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue x)) F (Metric.closedBall (0:E) 4))
    (hu : ∀i : HalfEndPhysicalSliceIndex,
      ((nativeH4CorrectedScaleJetCLM P hp v₀ hv hb (τ:=τ) T i x).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun y => Real.exp (3*i.1/2)*u (Real.exp (-i.1) • y))) :
    nativePhysicalShellAssembly (nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) g ε x (T x))
      =ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})]
      (fun y => nativePhysicalWeakJacobian g ε p.orbit p.phase u y-
        nativePhysicalWeakFlatJacobian p.orbit p.phase F y) := by
  rw [←nativePhysicalShell_union,ae_eq_restrict_iUnion_iff]
  intro n
  let s := nativeLogShellCenter n
  let i := nativeH4NonnegativeScaleIndex s (nativeLogShellCenter_nonneg n)
  have hr := nativeH4Residual_row_difference hκ0 hκ1 p hp τ g ε T x n
  have hd := ae_comp_dilation (Real.exp_ne_zero s) hr
  change (fun y => (nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) g ε x (T x) n : E→ℝ) (Real.exp s • y))
      =ᵐ[volume.restrict ((fun y : E => Real.exp s • y) ⁻¹' nativeSourceShell)] _ at hd
  rw [←nativePhysicalShell_dilation n] at hd
  have hn := nativeScaledJet_physical_operator g ε p.orbit p.smooth p.bounded p.phase s
    (nativeH4CorrectedScaleJetCLM P hp v₀ hv hb (τ:=τ) T i x) (hu i)
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

#print axioms nativeH4Residual_same_physical_operators
end Yamabe3.Analysis.UniformElliptic
