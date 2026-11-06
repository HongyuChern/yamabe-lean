import Yamabe3.Analysis.NativeCompactCutoffLaplacian
import Yamabe3.Analysis.NativeForcedEnergySpace

/-! The actual full conformal source of a compact closed collar H2 jet.
The same cutoff acts on the complete jet before differentiation. All
first/second product terms, scalar curvature, density and factor8 remain.
The C2 identities below supply the dense source witnesses. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix

def nativeCollarConformalDensityCLM (g:RiemannianMetric 3 E) : NativeCollarJet →L[ℝ] NativeCollarL2 :=
  (-8:ℝ) • nativeCollarDensityLaplacianCLM g+
    (nativeCollarScalarMulCLM (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x)
      ((native_density_smooth_positive g).1.continuous.mul g.leviCivitaData.contMDiff_scalarCurvature.continuous)).comp
      nativeCollarJetValueCLM

def nativeCompactConformalSourceCLM (g:RiemannianMetric 3 E) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    nativeCollarJetClosure →L[ℝ] Lp ℝ 2 (volume:Measure E) :=
  (l2ZeroExtendCLM nativePoissonEntranceCollar (nativePolarTimeWindow_open (1/2)).measurableSet).comp
    ((nativeCollarConformalDensityCLM g).comp ((nativeCollarCutoffRawCLM χ hχ).comp nativeCollarJetClosure.subtypeL))

theorem nativeCollarConformalDensity_C2_ae (g:RiemannianMetric 3 E) (u:nativeC2OffZero) :
    (nativeCollarConformalDensityCLM g (nativeC2CollarJetLinear u):E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun x=>g.pullbackVolumeDensity id x*(-8*g.leviCivitaData.laplacian u.val x+g.leviCivitaData.scalarCurvature x*u.val x) := by
  let J:=nativeC2CollarJetLinear u
  let A:=nativeCollarDensityLaplacianCLM g J
  let σ:=fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x
  let hσ:Continuous σ:=(native_density_smooth_positive g).1.continuous.mul g.leviCivitaData.contMDiff_scalarCurvature.continuous
  let B:=nativeCollarScalarMulCLM σ hσ J.1
  filter_upwards [Lp.coeFn_add ((-8:ℝ) • A) B,Lp.coeFn_smul (-8:ℝ) A,
    nativeCollarDensityLaplacian_C2_ae g u,nativeCollarScalarMulCLM_ae σ hσ J.1,
    (nativeC2Collar_memLp u.property).1.coeFn_toLp] with x hadd hsm hΔ hmul hu
  change (((-8:ℝ) • A)+B:NativeCollarL2) x=_
  rw [hadd]
  change ((-8:ℝ) • A) x+B x=_
  rw [hsm]
  change (-8:ℝ)*A x+B x=_
  change A x=g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian u.val x at hΔ
  change B x=σ x*J.1 x at hmul
  change (J.1:E→ℝ) x=u.val x at hu
  rw [hΔ,hmul,hu]
  dsimp only [σ]
  ring

theorem nativeCompactConformalSource_C2_ae (g:RiemannianMetric 3 E)
    {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) (hs:tsupport χ⊆nativePoissonEntranceCollar) (u:nativeC2OffZero) :
    (nativeCompactConformalSourceCLM g χ hχ (nativeC2CollarJetInclusion u):E→ℝ)=ᵐ[volume]
      fun x=>g.pullbackVolumeDensity id x*(-8*g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x+
        g.leviCivitaData.scalarCurvature x*(nativeC2Cutoff χ hχ u).val x) := by
  change (l2ZeroExtendCLM nativePoissonEntranceCollar (nativePolarTimeWindow_open (1/2)).measurableSet
    (nativeCollarConformalDensityCLM g (nativeCollarCutoffRawCLM χ hχ (nativeC2CollarJetLinear u))):E→ℝ)=ᵐ[volume] _
  rw [nativeCollarCutoffRawCLM_C2]
  have hh:=nativeCollarConformalDensity_C2_ae g (nativeC2Cutoff χ hχ u)
  have hi:=(ae_eq_restrict_iff_indicator_ae_eq (nativePolarTimeWindow_open (1/2)).measurableSet).mp hh
  apply ((l2ZeroExtend_ae nativePoissonEntranceCollar (nativePolarTimeWindow_open (1/2)).measurableSet _).trans hi).trans
  apply Eventually.of_forall
  intro x
  change nativePoissonEntranceCollar.indicator
    (fun y=>g.pullbackVolumeDensity id y*(-8*g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val y+
      g.leviCivitaData.scalarCurvature y*(nativeC2Cutoff χ hχ u).val y)) x=_
  by_cases hx:x∈nativePoissonEntranceCollar
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    change 0=g.pullbackVolumeDensity id x*(-8*g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x+
      g.leviCivitaData.scalarCurvature x*(nativeC2Cutoff χ hχ u).val x)
    rw [nativeC2Cutoff_laplacian_zero_off_collar g hχ hs u hx]
    have hz:χ x=0:=image_eq_zero_of_notMem_tsupport (fun h=>hx (hs h))
    simp only [nativeC2Cutoff,hz,zero_mul,mul_zero,add_zero]

theorem nativeCompactConformalValue_C2_ae
    {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) (hs:tsupport χ⊆nativePoissonEntranceCollar) (u:nativeC2OffZero) :
    (nativeCompactCollarValueCLM χ hχ (nativeC2CollarJetInclusion u):E→ℝ)=ᵐ[volume]
      (nativeC2Cutoff χ hχ u).val := by
  have hh:((nativeC2CollarJetInclusion u).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]u.val:=
    (nativeC2Collar_memLp u.property).1.coeFn_toLp
  have hi:nativePoissonEntranceCollar.indicator (fun x=>χ x*((nativeC2CollarJetInclusion u).val.1:E→ℝ) x)=ᵐ[volume]
      nativePoissonEntranceCollar.indicator (fun x=>χ x*u.val x):=
    (ae_eq_restrict_iff_indicator_ae_eq (nativePolarTimeWindow_open (1/2)).measurableSet).mp
      ((EventuallyEq.refl _ χ).mul hh)
  apply ((nativeCompactCollarValueCLM_ae χ hχ (nativeC2CollarJetInclusion u)).trans hi).trans
  apply Eventually.of_forall
  intro x
  change nativePoissonEntranceCollar.indicator (fun y=>χ y*u.val y) x=χ x*u.val x
  by_cases hx:x∈nativePoissonEntranceCollar
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport (fun h=>hx (hs h)),zero_mul]

#print axioms nativeCollarConformalDensity_C2_ae
#print axioms nativeCompactConformalSource_C2_ae
#print axioms nativeCompactConformalValue_C2_ae
end Yamabe3.Analysis.SpherePolar
