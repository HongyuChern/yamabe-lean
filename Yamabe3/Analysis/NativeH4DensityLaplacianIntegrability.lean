import Yamabe3.Analysis.WeightedH4SecondJetDecay
import Yamabe3.Analysis.OffZeroLocalIntegrability
import Yamabe3.Analysis.NativeH4GraphC1Removal
import Yamabe3.Analysis.NativeCollarDensityLaplacian
import Yamabe3.Analysis.C2PrincipalErrorPointwise

/-! The same genuine H4 graph representative has locally integrable
actual density-weighted native Laplacian. Integrability at the pole is
proved from its all-scale second-jet estimate, not a weak-PDE hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem nativeH4Graph_representative_weighted_slices
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    ∀s:ℝ,-Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s u.val) halfEndBasicAnnulus ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u.val) halfEndBasicAnnulus ≤ ENNReal.ofReal ‖v‖ := by
  intro s hs
  let i:HalfEndPhysicalSliceIndex:=⟨s,hs⟩
  have he:weightedPhysicalDilation s u.val=ᵐ[volume.restrict halfEndBasicAnnulus]
      halfEndWeightedPhysicalSliceMap v.1.1 i := by
    filter_upwards [ae_restrict_mem halfEndBasicAnnulus_isOpen.measurableSet] with x hx
    change Real.exp (3*s/2)*u.val (Real.exp (-s) • x)=
      Real.exp (3*s/2)*halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) (Real.exp (-s) • x)
    rw [hu (halfEnd_physical_slice_mem_entrance_ball i hx.2.le)]
  refine ⟨(MemWkp_congr_ae (by norm_num) halfEndBasicAnnulus_isOpen he).mpr (v.2 i).1,?_⟩
  rw [wkpNorm_congr_ae (k:=4) (by norm_num) halfEndBasicAnnulus_isOpen he]
  exact halfEndWeightedPhysicalSliceMap_norm_le v i

theorem nativeH4Graph_second_partials_locallyIntegrable
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    (i j:Fin 3) : LocallyIntegrable (partialDeriv i (partialDeriv j u.val)) volume := by
  have hc:ContinuousOn (partialDeriv i (partialDeriv j u.val)) ({(0:E)}ᶜ):=by
    intro x hx
    have hux:=u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
    have hp:ContDiffAt ℝ 1 (partialDeriv j u.val) x:=
      (hux.fderiv_right (by norm_num)).clm_apply contDiffAt_const
    have hpp:ContDiffAt ℝ 0 (partialDeriv i (partialDeriv j u.val)) x:=
      (hp.fderiv_right (by norm_num)).clm_apply contDiffAt_const
    exact hpp.continuousAt.continuousWithinAt
  obtain ⟨D,hD,hb⟩:=exists_weighted_H4_second_jet_decay_constant
  apply locallyIntegrable_of_offZero_inv_sqrt_bound hc
  intro x hx hn
  apply (norm_second_partial_le_second_at
    (u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)) i j).trans
  exact hb u.val u.property (ENNReal.ofReal ‖v‖) ENNReal.ofReal_ne_top
    (nativeH4Graph_representative_weighted_slices v u hu) x hx hn

theorem nativeH4Graph_density_laplacian_locallyIntegrable
    (g:RiemannianMetric 3 E) (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero)
    (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    LocallyIntegrable (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian u.val x) volume := by
  have hc:ContDiff ℝ 1 u.val:=(nativeH4Graph_representative_C1 v u h0 hu).1
  have hfirst(j:Fin 3):LocallyIntegrable (partialDeriv j u.val) volume:=
    ((hc.continuous_fderiv (by norm_num)).clm_apply continuous_const).locallyIntegrable
  have hsec(i j:Fin 3):LocallyIntegrable
      (fun x=>nativeDivergenceMatrix g x i j*partialDeriv i (partialDeriv j u.val) x) volume:=
    (nativeH4Graph_second_partials_locallyIntegrable v u hu i j).continuous_mul
      (contDiff_nativeDivergenceMatrix g i j).continuous
  have hfir(j:Fin 3):LocallyIntegrable
      (fun x=>nativeCollarDivergenceFirst g j x*partialDeriv j u.val x) volume:=
    (hfirst j).continuous_mul (continuous_nativeCollarDivergenceFirst g j)
  have hi:LocallyIntegrable
      (secondOrderOperator (nativeDivergenceMatrix g) (nativeCollarDivergenceFirst g) u.val) volume:=
    (locallyIntegrable_finsetSum _ (fun i _=>locallyIntegrable_finsetSum _ (fun j _=>hsec i j))).add
      (locallyIntegrable_finsetSum _ (fun j _=>hfir j))
  apply hi.congr
  filter_upwards [volume.ae_ne (0:E)] with x hx
  have hux:=u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
  have hd:=native_principalSource_eq_negative_density_laplacian_C2 g g.leviCivitaData hux
  have hp:=principalSource_eq_secondOrderOperator_C2_at (nativeCollarDivergenceFirst g)
    (contDiff_nativeDivergenceMatrix g) x hux
  simp only [nativeCollarDivergenceFirst,sub_self,zero_mul,Finset.sum_const_zero,add_zero] at hp
  linarith only [hd,hp]

#print axioms nativeH4Graph_representative_weighted_slices
#print axioms nativeH4Graph_second_partials_locallyIntegrable
#print axioms nativeH4Graph_density_laplacian_locallyIntegrable
end Yamabe3.Analysis.UniformElliptic
