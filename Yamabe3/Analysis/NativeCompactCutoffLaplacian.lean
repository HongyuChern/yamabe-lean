import Yamabe3.Analysis.NativeCompactC2Transposed
import Yamabe3.Analysis.NativeCompactCollarEnergyIdentity
import Yamabe3.Analysis.NativeCollarDensityLaplacian

/-! The actual compact collar C2 field has a genuine GLOBAL L2 density
Laplacian. It is the SAME zero-extended jet source. Outside the collar
its literal field is zero as a germ, so no unsupported point-mass or
boundary extension is asserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic

theorem nativeC2Cutoff_global_C2 {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ)
    (hs:tsupport χ⊆nativePoissonEntranceCollar) (u:nativeC2OffZero) :
    ContDiff ℝ 2 (nativeC2Cutoff χ hχ u).val := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx:x∈tsupport χ
  · have hx0:x≠0:=cylinderShell_ne_zero (nativeEntranceCollar_subset_shell (hs hx))
    exact (hχ.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).mul
      (u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx0))
  · have he:(fun y:E=>χ y*u.val y)=ᶠ[𝓝 x](fun _=>0):=by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem nativeC2Cutoff_laplacian_zero_off_collar (g:RiemannianMetric 3 E)
    {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) (hs:tsupport χ⊆nativePoissonEntranceCollar)
    (u:nativeC2OffZero) {x:E} (hx:x∉nativePoissonEntranceCollar) :
    g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x=0 := by
  have hxs:x∉tsupport χ:=fun h=>hx (hs h)
  have he:(nativeC2Cutoff χ hχ u).val=ᶠ[𝓝 x](fun _=>0):=by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxs] with y hy
    change χ y*u.val y=0
    rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
  rw [g.leviCivitaData.laplacian_eq_of_eventuallyEq he]
  simpa only [zero_mul] using g.leviCivitaData.laplacian_const_mul 0 (fun _:E=>0) x

theorem nativeC2Cutoff_density_laplacian_L2_identity (g:RiemannianMetric 3 E)
    {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) (hs:tsupport χ⊆nativePoissonEntranceCollar)
    (u:nativeC2OffZero) :
    (l2ZeroExtendCLM nativePoissonEntranceCollar (nativePolarTimeWindow_open (1/2)).measurableSet
      (nativeCollarDensityLaplacianCLM g (nativeC2CollarJetLinear (nativeC2Cutoff χ hχ u))):E→ℝ)
      =ᵐ[volume]fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x := by
  have hh:=nativeCollarDensityLaplacian_C2_ae g (nativeC2Cutoff χ hχ u)
  have hi:=(ae_eq_restrict_iff_indicator_ae_eq (nativePolarTimeWindow_open (1/2)).measurableSet).mp hh
  apply ((l2ZeroExtend_ae nativePoissonEntranceCollar (nativePolarTimeWindow_open (1/2)).measurableSet _).trans hi).trans
  apply Eventually.of_forall
  intro x
  change nativePoissonEntranceCollar.indicator
    (fun y=>g.pullbackVolumeDensity id y*g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val y) x=_
  by_cases hx:x∈nativePoissonEntranceCollar
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    change 0=g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x
    rw [nativeC2Cutoff_laplacian_zero_off_collar g hχ hs u hx,mul_zero]

theorem nativeC2Cutoff_density_laplacian_memLp (g:RiemannianMetric 3 E)
    {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) (hs:tsupport χ⊆nativePoissonEntranceCollar)
    (u:nativeC2OffZero) :
    MemLp (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x) 2 volume :=
  (Lp.memLp _).ae_eq (nativeC2Cutoff_density_laplacian_L2_identity g hχ hs u)

theorem nativeC2Cutoff_conformal_transposed (g:RiemannianMetric 3 E)
    {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆nativePoissonEntranceCollar)
    (u:nativeC2OffZero) (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hφc:HasCompactSupport φ) :
    (∫x,(nativeC2Cutoff χ hχ u).val x*(-8*g.leviCivitaData.laplacian φ x+g.leviCivitaData.scalarCurvature x*φ x) ∂g.volumeMeasure)=
      ∫x,(-8*g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x+
        g.leviCivitaData.scalarCurvature x*(nativeC2Cutoff χ hχ u).val x)*φ x ∂g.volumeMeasure :=
  native_compact_C2_conformal_transposed g (nativeC2Cutoff χ hχ u)
    ((nativeC2Cutoff_global_C2 hχ hs u).of_le (by norm_num)) hc.mul_right
    ((nativeC2Cutoff_density_laplacian_memLp g hχ hs u).locallyIntegrable (by norm_num)) φ hφ hφc

#print axioms nativeC2Cutoff_global_C2
#print axioms nativeC2Cutoff_laplacian_zero_off_collar
#print axioms nativeC2Cutoff_density_laplacian_L2_identity
#print axioms nativeC2Cutoff_density_laplacian_memLp
#print axioms nativeC2Cutoff_conformal_transposed
end Yamabe3.Analysis.SpherePolar
