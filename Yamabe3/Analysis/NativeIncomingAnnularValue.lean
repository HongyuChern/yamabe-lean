import Yamabe3.Analysis.NativeCoordinateCriticalCLM
import Yamabe3.Analysis.CriticalReceiverLinearDilation

/-! The SAME native H1 field has an actual scaled annular L2 value map
with uniform a^(-1/2) cost. This uses L6 and fixed chart density bounds,
not an unjustified C2 estimate outside the homogeneous receiving core. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def incomingValueH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] incomingValueH1Normed
private instance incomingValueSix:Fact (1 ≤ (6:ℝ≥0∞)) := ⟨by norm_num⟩

theorem exists_nativeIncoming_annular_value_CLM
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (O:Set E) (hvol:volume O < ⊤) :
    ∃C:ℝ,0 ≤ C ∧ ∀a:ℝ,0 < a →
      ∃T:H1Zero g.leviCivitaData univ →L[ℝ] Lp ℝ 2 (volume.restrict O),
        ‖T‖ ≤ C*Real.exp (-Real.log a/2) ∧ ∀W:H1Zero g.leviCivitaData univ,
          (T W:E→ℝ)=ᵐ[volume.restrict O]fun x:E=>
            nativeCoordinateZeroPullback e K (toL2 g.leviCivitaData univ W) (a • x) := by
  obtain ⟨D,hD,P,hP,hPv⟩:=exists_nativeCoordinate_critical_CLM g e he hei hK hKs
  obtain ⟨J,hJ,hdil⟩:=exists_criticalReceiver_dilation_CLM O hvol
  let E6:=GreenMass.NativeEnergyL6.toL6 g hY
  refine ⟨J*D*‖E6‖,by positivity,fun a ha=>?_⟩
  obtain ⟨R,hR,hRv⟩:=hdil (Real.log a)
  let T:=R.comp (P.comp E6)
  have hbound:‖T‖ ≤ (J*D*‖E6‖)*Real.exp (-Real.log a/2) := by
    apply (ContinuousLinearMap.opNorm_comp_le R (P.comp E6)).trans
    apply (mul_le_mul hR ((ContinuousLinearMap.opNorm_comp_le P E6).trans
      (mul_le_mul_of_nonneg_right hP (norm_nonneg E6))) (norm_nonneg (P.comp E6)) (by positivity)).trans_eq
    ring
  refine ⟨T,hbound,?_⟩
  intro W
  have h62:(E6 W:M→ℝ)=ᵐ[g.volumeMeasure](toL2 g.leviCivitaData univ W:M→ℝ) :=
    GreenMass.NativeEnergyL6.toL6_ae_toL2 g hY W
  have h2six:MemLp (toL2 g.leviCivitaData univ W:M→ℝ) 6 g.volumeMeasure :=
    (Lp.memLp (E6 W)).ae_eq h62
  have hpull:(P (E6 W):E→ℝ)=ᵐ[volume]nativeCoordinateZeroPullback e K (toL2 g.leviCivitaData univ W) :=
    (hPv (E6 W)).trans (nativeCoordinateZeroPullback_congr_six_ae g e he hei hK hKs (Lp.memLp (E6 W)) h2six h62)
  have hd:=ae_comp_dilation (Real.exp_ne_zero (Real.log a)) (ae_restrict_of_ae (s:=univ) hpull)
  simp only [preimage_univ,Measure.restrict_univ,Real.exp_log ha] at hd
  filter_upwards [hRv (P (E6 W)),ae_restrict_of_ae (s:=O) hd] with x hx hy
  change R (P (E6 W)) x=_
  rw [hx,Real.exp_log ha,hy]

#print axioms exists_nativeIncoming_annular_value_CLM
end Yamabe3.Analysis.SpherePolar
