import Yamabe3.Analysis.NativeScaledH4Integrability
import Yamabe3.Analysis.OffZeroCompactL2

/-! Local L2 of the actual scaled H4 field second derivatives and native
Laplacian. This supplies a source class for completed energy tests. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem iterated_scale (u:E→ℝ) (n:ℕ) {a:ℝ} (ha:a≠0) (x:E) :
    iteratedFDeriv ℝ n (fun y=>u (a • y)) x=a^n • iteratedFDeriv ℝ n u (a • x) := by
  let e:E≃L[ℝ]E:=(LinearEquiv.smulOfNeZero ℝ E a ha).toContinuousLinearEquiv
  have h:=e.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ (mem_univ (e x)) n
  simp only [preimage_univ,iteratedFDerivWithin_univ] at h
  change iteratedFDeriv ℝ n (fun y=>u (a • y)) x=_ at h
  rw [h]
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousMultilinearMap.smul_apply]
  change (iteratedFDeriv ℝ n u (a • x)) (fun i=>a • m i)=_
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

theorem nativeScaledH4_second_partials_memLp {a:ℝ} (ha:0<a)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    (i j:Fin 3) {K:Set E} (hK:IsCompact K) : MemLp (partialDeriv i (partialDeriv j (nativeScaledOffZero ha u).val)) 2 (volume.restrict K) := by
  let U:=nativeScaledOffZero ha u
  have hc:ContinuousOn (partialDeriv i (partialDeriv j U.val)) ({(0:E)}ᶜ):=by
    intro x hx
    have hux:=U.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
    have hp:ContDiffAt ℝ 1 (partialDeriv j U.val) x:=
      (hux.fderiv_right (by norm_num)).clm_apply contDiffAt_const
    have hpp:ContDiffAt ℝ 0 (partialDeriv i (partialDeriv j U.val)) x:=
      (hp.fderiv_right (by norm_num)).clm_apply contDiffAt_const
    exact hpp.continuousAt.continuousWithinAt
  obtain ⟨D,hD,hb⟩:=exists_weighted_H4_second_jet_decay_constant
  apply memLp_on_compact_of_offZero_inv_sqrt_bound hc ha (K:=K)
    (hK:=hK)
    (C:=a⁻¹^2*(D*(ENNReal.ofReal ‖v‖).toReal)/Real.sqrt a⁻¹)
  intro x hx hn
  apply (norm_second_partial_le_second_at
    (U.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)) i j).trans
  have hyn:‖a⁻¹ • x‖ ≤ 1:=by
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le]
    calc a⁻¹*‖x‖ ≤ a⁻¹*a := mul_le_mul_of_nonneg_left hn (inv_pos.mpr ha).le
         _ = 1 := inv_mul_cancel₀ ha.ne'
  have hbnd:=hb u.val u.property (ENNReal.ofReal ‖v‖) ENNReal.ofReal_ne_top
    (nativeH4Graph_representative_weighted_slices v u hu) (a⁻¹ • x)
    (smul_ne_zero (inv_ne_zero ha.ne') hx) hyn
  change ‖iteratedFDeriv ℝ 2 (fun y=>u.val (a⁻¹ • y)) x‖ ≤ _
  rw [iterated_scale u.val 2 (inv_ne_zero ha.ne'),norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ a⁻¹^2*(D*(ENNReal.ofReal ‖v‖).toReal/Real.sqrt ‖a⁻¹ • x‖) :=
      mul_le_mul_of_nonneg_left hbnd (sq_nonneg _)
    _ = _ := by
      rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le,Real.sqrt_mul (inv_pos.mpr ha).le]
      ring

theorem nativeScaledH4_density_laplacian_memLp
    (g:RiemannianMetric 3 E) {a:ℝ} (ha:0<a)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    {K:Set E} (hK:IsCompact K) :
    MemLp (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian (nativeScaledOffZero ha u).val x)
      2 (volume.restrict K) := by
  let U:=nativeScaledOffZero ha u
  letI:IsFiniteMeasure (volume.restrict K):=⟨by rw [Measure.restrict_apply_univ];exact hK.measure_lt_top⟩
  have hc:ContDiff ℝ 1 U.val:=nativeScaledH4_C1 ha v u h0 hu
  have hfirst(j:Fin 3):MemLp (partialDeriv j U.val) 2 (volume.restrict K):=
    (continuousOn_compact_memLp_top hK
      (((hc.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn)).mono_exponent (by simp)
  have hsec(i j:Fin 3):MemLp
      (fun x=>nativeDivergenceMatrix g x i j*partialDeriv i (partialDeriv j U.val) x) 2 (volume.restrict K):=
    (nativeScaledH4_second_partials_memLp ha v u hu i j hK).mul'
      (continuousOn_compact_memLp_top hK (contDiff_nativeDivergenceMatrix g i j).continuous.continuousOn)
  have hfir(j:Fin 3):MemLp
      (fun x=>nativeCollarDivergenceFirst g j x*partialDeriv j U.val x) 2 (volume.restrict K):=
    (hfirst j).mul' (continuousOn_compact_memLp_top hK (continuous_nativeCollarDivergenceFirst g j).continuousOn)
  have hi:MemLp (secondOrderOperator (nativeDivergenceMatrix g) (nativeCollarDivergenceFirst g) U.val) 2 (volume.restrict K):=
    (memLp_finsetSum _ (fun i _=>memLp_finsetSum _ (fun j _=>hsec i j))).add
      (memLp_finsetSum _ (fun j _=>hfir j))
  apply hi.ae_eq
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:E))] with x hx
  have hux:=U.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
  have hd:=native_principalSource_eq_negative_density_laplacian_C2 g g.leviCivitaData hux
  have hp:=principalSource_eq_secondOrderOperator_C2_at (nativeCollarDivergenceFirst g)
    (contDiff_nativeDivergenceMatrix g) x hux
  simp only [nativeCollarDivergenceFirst,sub_self,zero_mul,Finset.sum_const_zero,add_zero] at hp
  linarith only [hd,hp]

theorem nativeScaledH4_laplacian_memLp
    (g:RiemannianMetric 3 E) {a:ℝ} (ha:0<a)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    {K:Set E} (hK:IsCompact K) :
    MemLp (g.leviCivitaData.laplacian (nativeScaledOffZero ha u).val) 2 (volume.restrict K) := by
  have hp(x:E):0<g.pullbackVolumeDensity id x :=
    (g.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x) contMDiffAt_id (by simpa using Function.injective_id)).2
  have hc:Continuous (fun x:E=>(g.pullbackVolumeDensity id x)⁻¹):=by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((g.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x) contMDiffAt_id
      (by simpa using Function.injective_id)).1.continuousAt).inv₀ (hp x).ne'
  have hi:MemLp (fun x=>(g.pullbackVolumeDensity id x)⁻¹*
      (g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian (nativeScaledOffZero ha u).val x)) 2 (volume.restrict K):=
    (nativeScaledH4_density_laplacian_memLp g ha v u h0 hu hK).mul'
      (continuousOn_compact_memLp_top hK hc.continuousOn)
  apply hi.ae_eq
  exact Eventually.of_forall fun x=>by
    dsimp only
    rw [←mul_assoc,inv_mul_cancel₀ (hp x).ne',one_mul]

#print axioms nativeScaledH4_second_partials_memLp
#print axioms nativeScaledH4_density_laplacian_memLp
#print axioms nativeScaledH4_laplacian_memLp
end Yamabe3.Analysis.UniformElliptic
