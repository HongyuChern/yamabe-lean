/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Elliptic/Dirichlet/Coordinates.lean

Adapts the positive chart-density lower bound to the localized critical-exponent
pullback estimate.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.NativeChartCriticalTransport
import Yamabe3.Analysis.CriticalReceiverDilation
import GreenMass.NativeEnergyL6

/-! Actual compact coordinate pullback of the native L6 class, including
its density comparison. The constant is fixed before the input field;
this will give the critical a^(-1/2) incoming-source cost after dilation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

def nativeCoordinateZeroPullback (e:OpenPartialHomeomorph E M) (K:Set E) (f:M→ℝ) : E→ℝ :=
  K.indicator (fun x=>f (e x))

private theorem coordinate_mapback
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    Measure.map e ((volume.withDensity (fun x=>ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict e.source)=
      g.volumeMeasure.restrict e.target := by
  let ν:Measure E:=(volume.withDensity (fun x=>ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict e.source
  have hm:(g.volumeMeasure.restrict e.target).map e.symm=ν := g.map_restrict_volumeMeasure_symm e he hei
  have heν:AEMeasurable e ν := e.continuousOn.aemeasurable e.open_source.measurableSet
  have heiμ:AEMeasurable e.symm (g.volumeMeasure.restrict e.target) :=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  change ν.map e=_
  rw [←hm,AEMeasurable.map_map_of_aemeasurable (hm ▸ heν) heiμ]
  have hid:(e ∘ e.symm)=ᵐ[g.volumeMeasure.restrict e.target]id := by
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    exact e.right_inv hy
  rw [Measure.map_congr hid,Measure.map_id]

theorem exists_nativeCoordinate_zero_pullback_six_bound
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀f:M→ℝ,MemLp f 6 g.volumeMeasure →
      MemLp (nativeCoordinateZeroPullback e K f) 6 volume ∧
      eLpNorm (nativeCoordinateZeroPullback e K f) 6 volume ≤ C*eLpNorm f 6 g.volumeMeasure := by
  obtain hKe | hKne:=K.eq_empty_or_nonempty
  · subst K
    refine ⟨1,by simp,?_⟩
    intro f hf
    simp only [nativeCoordinateZeroPullback,indicator_empty']
    refine ⟨MemLp.zero,?_⟩
    rw [eLpNorm_zero]
    exact bot_le
  have hD:e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp),hei.mdifferentiableOn (by simp)⟩
  have hρ x (hx:x∈K):=g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds (hKs hx))) (hD.mfderiv_injective (hKs hx))
  obtain ⟨x,hx,hmin⟩:=hK.exists_isMinOn hKne
    (fun y hy=>(hρ y hy).1.continuousAt.continuousWithinAt)
  let c:=ENNReal.ofReal (g.pullbackVolumeDensity e x)
  have hc:c≠0 := (ENNReal.ofReal_pos.mpr (hρ x hx).2).ne'
  have hct:c≠⊤ := ENNReal.ofReal_ne_top
  let ν:Measure E:=(volume.withDensity (fun y=>ENNReal.ofReal (g.pullbackVolumeDensity e y))).restrict e.source
  have hmeasure:c • volume.restrict K ≤ ν := by
    calc
      _ = (volume.restrict K).withDensity (fun _=>c) := (withDensity_const c).symm
      _ ≤ (volume.restrict K).withDensity (fun y=>ENNReal.ofReal (g.pullbackVolumeDensity e y)) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
        exact ENNReal.ofReal_le_ofReal (hmin hy)
      _ = (volume.withDensity (fun y=>ENNReal.ofReal (g.pullbackVolumeDensity e y))).restrict K :=
        (restrict_withDensity hK.measurableSet _).symm
      _ ≤ _ := Measure.restrict_mono hKs le_rfl
  have hdom:volume.restrict K ≤ c⁻¹ • ν := by
    have hh:=smul_le_smul_left c⁻¹ hmeasure
    rw [smul_smul,ENNReal.inv_mul_cancel hc hct,one_smul] at hh
    exact hh
  let C:ℝ≥0∞:=c⁻¹^((1/(6:ℝ≥0∞)).toReal)
  have hC:C≠⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (ENNReal.inv_ne_top.mpr hc)
  refine ⟨C,hC,fun f hf=>?_⟩
  have heν:AEMeasurable e ν := e.continuousOn.aemeasurable e.open_source.measurableSet
  have hfmap:MemLp f 6 (ν.map e) := by
    rw [show ν.map e=g.volumeMeasure.restrict e.target from coordinate_mapback g e he hei]
    exact hf.restrict e.target
  have hp:MemLp (fun x:E=>f (e x)) 6 ν := hfmap.comp_of_map heν
  have hnorm:eLpNorm (fun x:E=>f (e x)) 6 ν=eLpNorm f 6 (g.volumeMeasure.restrict e.target) := by
    rw [←coordinate_mapback g e he hei]
    exact (eLpNorm_map_measure hfmap.1 heν).symm
  refine ⟨(memLp_indicator_iff_restrict hK.measurableSet).mpr
    (hp.of_measure_le_smul (ENNReal.inv_ne_top.mpr hc) hdom),?_⟩
  rw [nativeCoordinateZeroPullback,eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet]
  have hh:=eLpNorm_le_of_measure_le_smul (f:=fun x:E=>f (e x)) (p:=6) hdom
  rw [hnorm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (eLpNorm_mono_measure f Measure.restrict_le_self) zero_le)

#print axioms exists_nativeCoordinate_zero_pullback_six_bound
end Yamabe3.Analysis.SpherePolar
