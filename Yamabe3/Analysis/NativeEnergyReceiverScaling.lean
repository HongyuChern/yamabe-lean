import Yamabe3.Analysis.NativeChartSixPullback
import Yamabe3.Analysis.CriticalReceiverDilation

/-! The same native H1 element has a real rescaled local L2 receiving
bound. Its canonical L6 representative is already AE the native L2 one.
The H4/Cauchy norm and geometric equation still need their own proofs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def energyReceiverH1Normed (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] energyReceiverH1Normed

theorem exists_nativeEnergy_rescaled_receiver_L2_bound
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (O:Set E) (hO:MeasurableSet O) (hvol:volume O<⊤) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀(W:H1Zero g.leviCivitaData univ) (t:ℝ),
      MapsTo (fun x:E=>Real.exp t • x) O K→
      MemLp (fun x:E=>GreenMass.NativeEnergyL6.toL6 g hY W (e (Real.exp t • x))) 2 (volume.restrict O) ∧
      eLpNorm (fun x:E=>GreenMass.NativeEnergyL6.toL6 g hY W (e (Real.exp t • x))) 2 (volume.restrict O)≤
        C*ENNReal.ofReal (Real.exp (-t/2))*ENNReal.ofReal ‖W‖ := by
  obtain ⟨D,hD,hd⟩:=exists_nativeChart_six_pullback_bound g e he hei hK hKs
  obtain ⟨N,hN,hn⟩:=exists_criticalReceiver_dilation_L2_bound O hvol
  let T:=GreenMass.NativeEnergyL6.toL6 g hY
  refine ⟨N*D*ENNReal.ofReal ‖T‖,by finiteness,fun W t hmap=>?_⟩
  let v:=fun x:E=>T W (e x)
  let u:=K.indicator v
  have hv:=hd (T W)
  have hu:MemLp u 6 volume:=(memLp_indicator_iff_restrict hK.measurableSet).mpr hv.1
  have he:(fun x:E=>u (Real.exp t • x))=ᵐ[volume.restrict O](fun x:E=>v (Real.exp t • x)):=by
    filter_upwards [ae_restrict_mem hO] with x hx
    exact indicator_of_mem (hmap hx) _
  have hs:=hn u hu t
  refine ⟨hs.1.ae_eq he,?_⟩
  rw [←eLpNorm_congr_ae he]
  have hb:eLpNorm u 6 volume≤D*ENNReal.ofReal ‖T‖*ENNReal.ofReal ‖W‖:=by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet]
    calc
      _ ≤ D*ENNReal.ofReal ‖T W‖:=hv.2
      _ ≤ D*ENNReal.ofReal (‖T‖*‖W‖):=mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (T.le_opNorm W)) zero_le zero_le
      _ = _:=by rw [ENNReal.ofReal_mul (norm_nonneg _)];ring
  exact hs.2.trans ((mul_le_mul le_rfl hb zero_le zero_le).trans_eq (by ring))

#print axioms exists_nativeEnergy_rescaled_receiver_L2_bound
end Yamabe3.Analysis.SpherePolar
