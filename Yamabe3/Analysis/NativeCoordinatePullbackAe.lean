import Yamabe3.Analysis.NativeCoordinateCriticalPullback

/-! The compact coordinate L6 pullback preserves actual native a.e.
identity. Consequently addition, scaling and the native H1 L2/L6
realizations can be transported without evaluating an arbitrary Lp class. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

def nativeCoordinateZeroPullbackLinear (e:OpenPartialHomeomorph E M) (K:Set E) :
    (M→ℝ) →ₗ[ℝ] (E→ℝ) where
  toFun:=nativeCoordinateZeroPullback e K
  map_add' f h:=by
    ext x
    by_cases hx:x∈K
    · simp only [nativeCoordinateZeroPullback,indicator_of_mem hx,Pi.add_apply]
    · simp only [nativeCoordinateZeroPullback,indicator_of_notMem hx,Pi.add_apply,add_zero]
  map_smul' c f:=by
    simp only [RingHom.id_apply]
    ext x
    by_cases hx:x∈K
    · simp only [nativeCoordinateZeroPullback,indicator_of_mem hx,Pi.smul_apply]
    · simp only [nativeCoordinateZeroPullback,indicator_of_notMem hx,Pi.smul_apply,smul_zero]

theorem nativeCoordinateZeroPullback_congr_six_ae
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {f h:M→ℝ} (hf:MemLp f 6 g.volumeMeasure) (hh:MemLp h 6 g.volumeMeasure)
    (hfh:f=ᵐ[g.volumeMeasure]h) :
    nativeCoordinateZeroPullback e K f=ᵐ[volume]nativeCoordinateZeroPullback e K h := by
  obtain ⟨C,hC,hb⟩:=exists_nativeCoordinate_zero_pullback_six_bound g e he hei hK hKs
  have hz:(f-h)=ᵐ[g.volumeMeasure](0:M→ℝ) := hfh.mono (fun x hx=>by simp only [Pi.sub_apply,Pi.zero_apply,hx,sub_self])
  have hnorm:eLpNorm (f-h) 6 g.volumeMeasure=0 := by rw [eLpNorm_congr_ae hz,eLpNorm_zero]
  have hp:=hb (f-h) (hf.sub hh)
  have hzero:eLpNorm (nativeCoordinateZeroPullback e K (f-h)) 6 volume=0 := by
    apply le_antisymm ?_ (by positivity)
    simpa only [hnorm,mul_zero] using hp.2
  have hae: nativeCoordinateZeroPullback e K (f-h)=ᵐ[volume](0:E→ℝ) :=
    (eLpNorm_eq_zero_iff hp.1.1 (by norm_num:(6:ℝ≥0∞)≠0)).mp hzero
  filter_upwards [hae] with x hx
  by_cases hk:x∈K
  · simp only [nativeCoordinateZeroPullback,indicator_of_mem hk,Pi.sub_apply,Pi.zero_apply] at hx ⊢
    exact sub_eq_zero.mp hx
  · simp only [nativeCoordinateZeroPullback,indicator_of_notMem hk]

#print axioms nativeCoordinateZeroPullbackLinear
#print axioms nativeCoordinateZeroPullback_congr_six_ae
end Yamabe3.Analysis.SpherePolar
