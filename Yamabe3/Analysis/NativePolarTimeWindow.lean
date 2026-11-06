import Yamabe3.Analysis.Cylinder.NativeHalfEndPolarEnergy

/-! Actual log-polar integration on an arbitrary measurable time window.
This extends the prior half-end transfer without changing its measure. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar

def nativePolarTimeWindow (T : Set ℝ) : Set E :=
  {x | x ≠ 0 ∧ -Real.log ‖x‖ ∈ T}

theorem nativePolarTimeWindow_measurable {T : Set ℝ} (hT : MeasurableSet T) :
    MeasurableSet (nativePolarTimeWindow T) := by
  exact (measurableSet_singleton (0:E)).compl.inter
    (hT.preimage (measurable_norm.log.neg))

theorem cylinderPoint_mem_timeWindow_iff (T : Set ℝ) (p : ℝ × S) :
    cylinderPoint p ∈ nativePolarTimeWindow T ↔ p.1 ∈ T := by
  change (cylinderPoint p ≠ 0 ∧ -Real.log ‖cylinderPoint p‖ ∈ T) ↔ p.1 ∈ T
  rw [cylinderPoint_norm,Real.log_exp,neg_neg]
  exact and_iff_right (cylinderPoint_ne_zero p)


theorem native_timeWindow_integrable_and_integral_of_angular_energy
    (T : Set ℝ) (hT : MeasurableSet T)
    {g : E → ℝ} {h : ℝ → ℝ}
    (hg : ContinuousOn g (nativePolarTimeWindow T))
    (hgn : ∀ x ∈ nativePolarTimeWindow T, 0 ≤ g x)
    (hh : IntegrableOn h T)
    (he : ∀ t : ℝ, t ∈ T →
      (∫ θ : S, Real.exp (-3 * t) * g (cylinderPoint (t, θ)) ∂angularVolume) = h t) :
    IntegrableOn g (nativePolarTimeWindow T) ∧
      (∫ x in nativePolarTimeWindow T, g x) = ∫ t in T, h t := by
  classical
  let O := nativePolarTimeWindow T
  let G := O.indicator g
  have hO : MeasurableSet O := nativePolarTimeWindow_measurable hT
  have hG : Measurable G := by
    have heq : G = O.piecewise g (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ O <;> simp [G, hx]
    rw [heq]
    exact hg.measurable_piecewise continuousOn_const hO
  have hL : Measurable (logCylinderWeight G) := measurable_logCylinderWeight hG
  have hpos (t : ℝ) (ht : t ∈ T) (θ : S) :
      logCylinderWeight G (t, θ) = Real.exp (-3 * t) * g (cylinderPoint (t, θ)) := by
    change Real.exp (-3 * t) * O.indicator g (cylinderPoint (t, θ)) = _
    rw [Set.indicator_of_mem ((cylinderPoint_mem_timeWindow_iff T (t, θ)).mpr ht)]
  have hnonpos (t : ℝ) (ht : ¬ t ∈ T) (θ : S) :
      logCylinderWeight G (t, θ) = 0 := by
    change Real.exp (-3 * t) * O.indicator g (cylinderPoint (t, θ)) = _
    rw [Set.indicator_of_notMem
      (fun hx => ht ((cylinderPoint_mem_timeWindow_iff T (t, θ)).mp hx)), mul_zero]
  have hLnonneg (t : ℝ) (θ : S) : 0 ≤ logCylinderWeight G (t, θ) := by
    by_cases ht : t ∈ T
    · rw [hpos t ht θ]
      exact mul_nonneg (Real.exp_pos _).le
        (hgn _ ((cylinderPoint_mem_timeWindow_iff T (t, θ)).mpr ht))
    · rw [hnonpos t ht θ]
  have hs (t : ℝ) : Integrable (fun θ : S => logCylinderWeight G (t, θ)) angularVolume := by
    by_cases ht : t ∈ T
    · have hc : Continuous (fun θ : S => g (cylinderPoint (t, θ))) :=
        hg.comp_continuous (continuous_cylinderPoint.comp (continuous_const.prodMk continuous_id))
          (fun θ => (cylinderPoint_mem_timeWindow_iff T (t, θ)).mpr ht)
      have hi := (hc.const_mul (Real.exp (-3 * t))).integrable_of_hasCompactSupport
        (μ := angularVolume)
        (HasCompactSupport.of_compactSpace _)
      exact hi.congr (Eventually.of_forall fun θ => (hpos t ht θ).symm)
    · have hz : (fun θ : S => logCylinderWeight G (t, θ)) = 0 := funext (hnonpos t ht)
      rw [hz]
      exact integrable_zero _ _ _
  have hinner (t : ℝ) : (∫ θ : S, logCylinderWeight G (t, θ) ∂angularVolume) =
      (T).indicator h t := by
    by_cases ht : t ∈ T
    · rw [Set.indicator_of_mem (show t ∈ T from ht)]
      exact (integral_congr_ae (Eventually.of_forall (hpos t ht))).trans (he t ht)
    · rw [Set.indicator_of_notMem (show t ∉ T from ht)]
      exact integral_eq_zero_of_ae (Eventually.of_forall (hnonpos t ht))
  have hnorm (t : ℝ) : (∫ θ : S, ‖logCylinderWeight G (t, θ)‖ ∂angularVolume) =
      (T).indicator h t := by
    calc
      _ = ∫ θ : S, logCylinderWeight G (t, θ) ∂angularVolume :=
        integral_congr_ae (Eventually.of_forall fun θ => Real.norm_of_nonneg (hLnonneg t θ))
      _ = _ := hinner t
  have hprod : Integrable (logCylinderWeight G) (volume.prod angularVolume) := by
    apply (integrable_prod_iff hL.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hs, ?_⟩
    have hI : Integrable ((T).indicator h) (volume : Measure ℝ) :=
      (integrable_indicator_iff hT).mpr hh
    simpa only [hnorm] using hI
  have hi : Integrable G := (integrable_euclidean_iff_cylinder hG).mpr hprod
  refine ⟨(integrable_indicator_iff hO).mp hi, ?_⟩
  calc
    _ = ∫ x : E, G x := (integral_indicator hO).symm
    _ = ∫ t : ℝ, ∫ θ : S, logCylinderWeight G (t, θ) ∂angularVolume :=
      integral_euclidean_eq_cylinder_of_pullback hG hprod
    _ = ∫ t : ℝ, (T).indicator h t := by simp_rw [hinner]
    _ = _ := integral_indicator hT


#print axioms native_timeWindow_integrable_and_integral_of_angular_energy
end Yamabe3.Analysis.SpherePolar
