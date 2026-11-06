import Yamabe3.Analysis.Cylinder.NativeLogPolarIntegrals
import Yamabe3.Analysis.Cylinder.NativeCylinderTest
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Genuine polar transfer for nonnegative physical energy densities

Continuity is needed only on the punctured unit ball.  Its indicator is
measurable, and each actual angular section is integrable by compactness
of the native sphere.  A proved positive-time angular integral, together
with its real integrability, therefore produces integrability of the
original Euclidean density and its exact global integral.

This transfer will consume actual finite-gradient identities.  It does
not assume a Euclidean gradient bound or identify any spectral proxy
with a physical derivative.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

theorem cylinderPoint_mem_halfEnd_iff (p : ℝ × S) :
    cylinderPoint p ∈ Metric.ball (0 : E) 1 \ {(0 : E)} ↔ 0 < p.1 := by
  simp only [mem_diff, Metric.mem_ball, dist_zero_right, cylinderPoint_norm,
    mem_singleton_iff, cylinderPoint_ne_zero p, not_false_eq_true, and_true]
  rw [← Real.exp_zero, Real.exp_lt_exp]
  exact neg_lt_zero

/-- A nonnegative actual physical density with an integrable actual
angular integral has exactly that global polar energy on B1 minus zero. -/
theorem native_halfEnd_integrable_and_integral_of_angular_energy
    {g : E → ℝ} {h : ℝ → ℝ}
    (hg : ContinuousOn g (Metric.ball (0 : E) 1 \ {(0 : E)}))
    (hgn : ∀ x ∈ Metric.ball (0 : E) 1 \ {(0 : E)}, 0 ≤ g x)
    (hh : IntegrableOn h (Ioi 0))
    (he : ∀ t : ℝ, 0 < t →
      (∫ θ : S, Real.exp (-3 * t) * g (cylinderPoint (t, θ)) ∂angularVolume) = h t) :
    IntegrableOn g (Metric.ball (0 : E) 1 \ {(0 : E)}) ∧
      (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, g x) = ∫ t in Ioi (0 : ℝ), h t := by
  classical
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let G := O.indicator g
  have hO : MeasurableSet O := (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hG : Measurable G := by
    have heq : G = O.piecewise g (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ O <;> simp [G, hx]
    rw [heq]
    exact hg.measurable_piecewise continuousOn_const hO
  have hL : Measurable (logCylinderWeight G) := measurable_logCylinderWeight hG
  have hpos (t : ℝ) (ht : 0 < t) (θ : S) :
      logCylinderWeight G (t, θ) = Real.exp (-3 * t) * g (cylinderPoint (t, θ)) := by
    change Real.exp (-3 * t) * O.indicator g (cylinderPoint (t, θ)) = _
    rw [Set.indicator_of_mem ((cylinderPoint_mem_halfEnd_iff (t, θ)).mpr ht)]
  have hnonpos (t : ℝ) (ht : ¬ 0 < t) (θ : S) :
      logCylinderWeight G (t, θ) = 0 := by
    change Real.exp (-3 * t) * O.indicator g (cylinderPoint (t, θ)) = _
    rw [Set.indicator_of_notMem
      (fun hx => ht ((cylinderPoint_mem_halfEnd_iff (t, θ)).mp hx)), mul_zero]
  have hLnonneg (t : ℝ) (θ : S) : 0 ≤ logCylinderWeight G (t, θ) := by
    by_cases ht : 0 < t
    · rw [hpos t ht θ]
      exact mul_nonneg (Real.exp_pos _).le
        (hgn _ ((cylinderPoint_mem_halfEnd_iff (t, θ)).mpr ht))
    · rw [hnonpos t ht θ]
  have hs (t : ℝ) : Integrable (fun θ : S => logCylinderWeight G (t, θ)) angularVolume := by
    by_cases ht : 0 < t
    · have hc : Continuous (fun θ : S => g (cylinderPoint (t, θ))) :=
        hg.comp_continuous (continuous_cylinderPoint.comp (continuous_const.prodMk continuous_id))
          (fun θ => (cylinderPoint_mem_halfEnd_iff (t, θ)).mpr ht)
      have hi := (hc.const_mul (Real.exp (-3 * t))).integrable_of_hasCompactSupport
        (μ := angularVolume)
        (HasCompactSupport.of_compactSpace _)
      exact hi.congr (Eventually.of_forall fun θ => (hpos t ht θ).symm)
    · have hz : (fun θ : S => logCylinderWeight G (t, θ)) = 0 := funext (hnonpos t ht)
      rw [hz]
      exact integrable_zero _ _ _
  have hinner (t : ℝ) : (∫ θ : S, logCylinderWeight G (t, θ) ∂angularVolume) =
      (Ioi (0 : ℝ)).indicator h t := by
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      exact (integral_congr_ae (Eventually.of_forall (hpos t ht))).trans (he t ht)
    · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
      exact integral_eq_zero_of_ae (Eventually.of_forall (hnonpos t ht))
  have hnorm (t : ℝ) : (∫ θ : S, ‖logCylinderWeight G (t, θ)‖ ∂angularVolume) =
      (Ioi (0 : ℝ)).indicator h t := by
    calc
      _ = ∫ θ : S, logCylinderWeight G (t, θ) ∂angularVolume :=
        integral_congr_ae (Eventually.of_forall fun θ => Real.norm_of_nonneg (hLnonneg t θ))
      _ = _ := hinner t
  have hprod : Integrable (logCylinderWeight G) (volume.prod angularVolume) := by
    apply (integrable_prod_iff hL.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hs, ?_⟩
    have hI : Integrable ((Ioi (0 : ℝ)).indicator h) (volume : Measure ℝ) :=
      (integrable_indicator_iff measurableSet_Ioi).mpr hh
    simpa only [hnorm] using hI
  have hi : Integrable G := (integrable_euclidean_iff_cylinder hG).mpr hprod
  refine ⟨(integrable_indicator_iff hO).mp hi, ?_⟩
  calc
    _ = ∫ x : E, G x := (integral_indicator hO).symm
    _ = ∫ t : ℝ, ∫ θ : S, logCylinderWeight G (t, θ) ∂angularVolume :=
      integral_euclidean_eq_cylinder_of_pullback hG hprod
    _ = ∫ t : ℝ, (Ioi (0 : ℝ)).indicator h t := by simp_rw [hinner]
    _ = _ := integral_indicator measurableSet_Ioi

/-- A genuine finite angular identity for the actual coordinate gradient
produces global L2 membership of each original classical partial. -/
theorem native_halfEnd_gradient_memLp_of_angular_energy
    {u : E → ℝ} {h : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Metric.ball (0 : E) 1 \ {(0 : E)}))
    (hh : IntegrableOn h (Ioi 0))
    (he : ∀ t : ℝ, 0 < t →
      (∫ θ : S, Real.exp (-3 * t) *
        (∑ i : Fin 3, (fderiv ℝ u (cylinderPoint (t, θ))
          (EuclideanSpace.single i 1)) ^ 2) ∂angularVolume) = h t) :
    (∀ i : Fin 3, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)}))) ∧
      (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
        ∑ i : Fin 3, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) =
        ∫ t in Ioi (0 : ℝ), h t := by
  classical
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let g : E → ℝ := fun x => ∑ i : Fin 3,
    (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have hp (i : Fin 3) : ContinuousOn
      (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) O :=
    (hu.continuousOn_fderiv_of_isOpen hO (by norm_num)).clm_apply continuousOn_const
  have hg : ContinuousOn g O := continuousOn_finsetSum _ (fun i _ => (hp i).pow 2)
  have hgn (x : E) : 0 ≤ g x := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  obtain ⟨hgI, hge⟩ := native_halfEnd_integrable_and_integral_of_angular_energy
    hg (fun x _hx => hgn x) hh he
  refine ⟨fun i => ?_, hge⟩
  apply (memLp_two_iff_integrable_sq
    ((hp i).aestronglyMeasurable (μ := volume) hO.measurableSet)).mpr
  apply hgI.mono' (((hp i).pow 2).aestronglyMeasurable (μ := volume) hO.measurableSet)
  exact Eventually.of_forall fun x => by
    change ‖(fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2‖ ≤ g x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun j : Fin 3 =>
      (fderiv ℝ u x (EuclideanSpace.single j 1)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)

#print axioms cylinderPoint_mem_halfEnd_iff
#print axioms native_halfEnd_integrable_and_integral_of_angular_energy
#print axioms native_halfEnd_gradient_memLp_of_angular_energy

end Yamabe3.Analysis.SpherePolar
