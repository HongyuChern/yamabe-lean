import Yamabe3.Analysis.NativeH4DensityLaplacianIntegrability

/-! The same H4 field at its actual positive physical scale retains C1
regularity and locally integrable classical second derivatives. No
second derivative at the pole and no weak equation are assumed. -/
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

private theorem locallyIntegrable_inv_sqrt_near {F:E→ℝ}
    (hc:ContinuousOn F ({(0:E)}ᶜ)) {C a:ℝ} (ha:0<a)
    (hb:∀x:E,x≠0 → ‖x‖ ≤ a → ‖F x‖ ≤ C/Real.sqrt ‖x‖) :
    LocallyIntegrable F volume := by
  have hm:Measurable F:=hc.measurable_of_countable_compl (by
    simpa only [compl_compl] using countable_singleton (0:E))
  have hball:IntegrableOn F (ball (0:E) a) volume:=by
    apply integrableOn_ball_of_norm_le_rpow (α:=(1/2:ℝ)) (by simp) (by norm_num)
      (C:=C) ?_ hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0:E))] with x hx hx0
    have hn:‖x‖ ≤ a:=(by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<a).le
    simpa only [Real.rpow_neg (norm_nonneg x),Real.sqrt_eq_rpow,div_eq_mul_inv] using hb x hx0 hn
  intro x
  by_cases hx:x=0
  · subst x
    exact ⟨ball (0:E) a,Metric.ball_mem_nhds _ ha,hball⟩
  · have hi:=hc.integrableAt_nhdsWithin (μ:=volume) isClosed_singleton.isOpen_compl.measurableSet hx
    rwa [nhdsWithin_eq_nhds.mpr (isClosed_singleton.isOpen_compl.mem_nhds hx)] at hi

def nativeScaledOffZero {a:ℝ} (ha:0<a) (u:nativeC2OffZero) : nativeC2OffZero:=
  ⟨fun x=>u.val (a⁻¹ • x),by
    apply u.property.comp (contDiff_id.const_smul a⁻¹).contDiffOn
    intro x hx
    exact smul_ne_zero (inv_ne_zero ha.ne') hx⟩

theorem nativeScaledH4_C1 {a:ℝ} (ha:0<a)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    ContDiff ℝ 1 (nativeScaledOffZero ha u).val :=
  (nativeH4Graph_representative_C1 v u h0 hu).1.comp (contDiff_id.const_smul _)

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

theorem nativeScaledH4_second_partials_locallyIntegrable {a:ℝ} (ha:0<a)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    (i j:Fin 3) : LocallyIntegrable (partialDeriv i (partialDeriv j (nativeScaledOffZero ha u).val)) volume := by
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
  apply locallyIntegrable_inv_sqrt_near hc ha
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

theorem nativeScaledH4_density_laplacian_locallyIntegrable
    (g:RiemannianMetric 3 E) {a:ℝ} (ha:0<a)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    LocallyIntegrable (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian (nativeScaledOffZero ha u).val x) volume := by
  let U:=nativeScaledOffZero ha u
  have hc:ContDiff ℝ 1 U.val:=nativeScaledH4_C1 ha v u h0 hu
  have hfirst(j:Fin 3):LocallyIntegrable (partialDeriv j U.val) volume:=
    ((hc.continuous_fderiv (by norm_num)).clm_apply continuous_const).locallyIntegrable
  have hsec(i j:Fin 3):LocallyIntegrable
      (fun x=>nativeDivergenceMatrix g x i j*partialDeriv i (partialDeriv j U.val) x) volume:=
    (nativeScaledH4_second_partials_locallyIntegrable ha v u hu i j).continuous_mul
      (contDiff_nativeDivergenceMatrix g i j).continuous
  have hfir(j:Fin 3):LocallyIntegrable
      (fun x=>nativeCollarDivergenceFirst g j x*partialDeriv j U.val x) volume:=
    (hfirst j).continuous_mul (continuous_nativeCollarDivergenceFirst g j)
  have hi:LocallyIntegrable
      (secondOrderOperator (nativeDivergenceMatrix g) (nativeCollarDivergenceFirst g) U.val) volume:=
    (locallyIntegrable_finsetSum _ (fun i _=>locallyIntegrable_finsetSum _ (fun j _=>hsec i j))).add
      (locallyIntegrable_finsetSum _ (fun j _=>hfir j))
  apply hi.congr
  filter_upwards [volume.ae_ne (0:E)] with x hx
  have hux:=U.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
  have hd:=native_principalSource_eq_negative_density_laplacian_C2 g g.leviCivitaData hux
  have hp:=principalSource_eq_secondOrderOperator_C2_at (nativeCollarDivergenceFirst g)
    (contDiff_nativeDivergenceMatrix g) x hux
  simp only [nativeCollarDivergenceFirst,sub_self,zero_mul,Finset.sum_const_zero,add_zero] at hp
  linarith only [hd,hp]

#print axioms nativeScaledH4_C1
#print axioms nativeScaledH4_second_partials_locallyIntegrable
#print axioms nativeScaledH4_density_laplacian_locallyIntegrable
end Yamabe3.Analysis.UniformElliptic
