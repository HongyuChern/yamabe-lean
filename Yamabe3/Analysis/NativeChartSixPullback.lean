/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Elliptic/Dirichlet/Coordinates.lean

Adapts the positive lower-bound calculation for chart volume density to a quantitative
L6 pullback bound.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.NativeChartCriticalTransport

/-! Quantitative L6 pullback of the same native energy class. A positive
lower density bound, not only an upper bound, pays for Euclidean volume. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeChart_six_pullback_density
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (v:Lp ℝ 6 g.volumeMeasure) :
    let μ:=((volume.withDensity (fun x=>ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict e.source)
    MemLp (fun x=>v (e x)) 6 μ ∧ eLpNorm (fun x=>v (e x)) 6 μ≤ENNReal.ofReal ‖v‖ := by
  dsimp only
  rw [←g.map_restrict_volumeMeasure_symm e he hei]
  have hm:AEStronglyMeasurable (fun x=>v (e x)) ((g.volumeMeasure.restrict e.target).map e.symm):=by
    rw [g.map_restrict_volumeMeasure_symm e he hei]
    exact ((Lp.stronglyMeasurable v).measurable.comp_aemeasurable
      (e.continuousOn.aemeasurable e.open_source.measurableSet)).aestronglyMeasurable
  have hs:AEMeasurable e.symm (g.volumeMeasure.restrict e.target):=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  have ha:((fun x=>v (e x)) ∘ e.symm)=ᵐ[g.volumeMeasure.restrict e.target](v:M→ℝ):=by
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    simp only [Function.comp_apply,e.right_inv hy]
  refine ⟨(memLp_map_measure_iff hm hs).mpr (((Lp.memLp v).restrict e.target).ae_eq ha.symm),?_⟩
  rw [eLpNorm_map_measure hm hs,eLpNorm_congr_ae ha]
  exact (eLpNorm_mono_measure v Measure.restrict_le_self).trans_eq (by rw [←Lp.enorm_def,←ofReal_norm])

theorem exists_nativeChart_six_pullback_bound
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀v:Lp ℝ 6 g.volumeMeasure,
      MemLp (fun x=>v (e x)) 6 (volume.restrict K) ∧
      eLpNorm (fun x=>v (e x)) 6 (volume.restrict K)≤C*ENNReal.ofReal ‖v‖ := by
  obtain hKe|hKne:=K.eq_empty_or_nonempty
  · refine ⟨1,by norm_num,fun v=>?_⟩
    simp [hKe]
  have hD:e.MDifferentiable (𝓡 3) (𝓡 3):=
    ⟨he.mdifferentiableOn (by simp),hei.mdifferentiableOn (by simp)⟩
  have hρ (x) (hx:x∈K):=g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds (hKs hx))) (hD.mfderiv_injective (hKs hx))
  obtain ⟨x,hx,hmin⟩:=hK.exists_isMinOn hKne
    (fun y hy=>(hρ y hy).1.continuousAt.continuousWithinAt)
  let c:=ENNReal.ofReal (g.pullbackVolumeDensity e x)
  have hc:c≠0:=(ENNReal.ofReal_pos.mpr (hρ x hx).2).ne'
  have hct:c≠⊤:=ENNReal.ofReal_ne_top
  have hmeasure:c • volume.restrict K≤
      (volume.withDensity (fun y=>ENNReal.ofReal (g.pullbackVolumeDensity e y))).restrict e.source:=by
    calc
      _ = (volume.restrict K).withDensity (fun _=>c):=(withDensity_const c).symm
      _ ≤ (volume.restrict K).withDensity (fun y=>ENNReal.ofReal (g.pullbackVolumeDensity e y)):=by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
        exact ENNReal.ofReal_le_ofReal (hmin hy)
      _ = (volume.withDensity (fun y=>ENNReal.ofReal (g.pullbackVolumeDensity e y))).restrict K:=
        (restrict_withDensity hK.measurableSet _).symm
      _ ≤ _:=Measure.restrict_mono hKs le_rfl
  have hb:=smul_le_smul_left c⁻¹ hmeasure
  rw [smul_smul,ENNReal.inv_mul_cancel hc hct,one_smul] at hb
  refine ⟨c⁻¹^((1/(6:ℝ≥0∞)).toReal),ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (ENNReal.inv_ne_top.mpr hc),fun v=>?_⟩
  have hv:=nativeChart_six_pullback_density g e he hei v
  exact ⟨hv.1.of_measure_le_smul (ENNReal.inv_ne_top.mpr hc) hb,
    (eLpNorm_le_of_measure_le_smul hb).trans (mul_le_mul le_rfl hv.2 zero_le zero_le)⟩

#print axioms nativeChart_six_pullback_density
#print axioms exists_nativeChart_six_pullback_bound
end Yamabe3.Analysis.SpherePolar
