import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndPhysicalL2
import Yamabe3.Analysis.HilbertFiniteProjectionFilter

/-!
# Global physical L2 convergence of the original finite spectral net

The exact polar identity is applied to the same projected joint
representative minus the original representative.  Dominated convergence
uses the actual integrable weighted Hilbert norm on the entire positive
half-line.  Thus the conclusion concerns the whole punctured unit ball,
not merely each fixed shell.  The source error retains its exact factor
64 and all finite sets are the original spectral finite sets.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem native_halfEnd_weighted_norm_integrable_of_bound
    {U : ℝ → AngularL2} (hU : Continuous U) (B : ℝ)
    (hbound : ∀ t, 0 ≤ t → ‖U t‖ ≤ B) :
    IntegrableOn (fun t => Real.exp (-2 * t) * ‖U t‖ ^ 2) (Ioi 0) := by
  have hmajor : IntegrableOn (fun t : ℝ => B ^ 2 * Real.exp (-2 * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).const_mul (B ^ 2)
  apply hmajor.mono'
    (((show Continuous (fun t : ℝ => Real.exp (-2 * t)) by fun_prop).mul
      (hU.norm.pow 2)).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖Real.exp (-2 * t) * ‖U t‖ ^ 2‖ ≤ B ^ 2 * Real.exp (-2 * t)
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hbound t ht.le) 2) (Real.exp_pos _).le).trans_eq
      (mul_comm _ _)

/-- An actual weighted Hilbert square integral supplies the global
physical L2 error limit along the same cofinal finite-set family. -/
theorem native_halfEnd_global_projection_error_tendsto
    {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
    {s : J → Finset AngularIndex} (hs : Tendsto s l atTop)
    {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    (htime : IntegrableOn (fun t => Real.exp (-2 * t) * ‖U t‖ ^ 2) (Ioi 0)) :
    Tendsto (fun j => ∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
      (cylinderLift (projectedAngular (s j) U) x - cylinderLift w x) ^ 2) l (𝓝 0) := by
  let error (j : J) (t : ℝ) := Real.exp (-2 * t) *
    ‖finiteHilbertProjection angularBasis (s j) (U t) - U t‖ ^ 2
  let major (t : ℝ) := 4 * (Real.exp (-2 * t) * ‖U t‖ ^ 2)
  have hmajor : Integrable major (volume.restrict (Ioi 0)) := htime.const_mul 4
  have herrorm (j : J) : AEStronglyMeasurable (error j) (volume.restrict (Ioi 0)) :=
    (((show Continuous (fun t : ℝ => Real.exp (-2 * t)) by fun_prop).mul
      ((((continuous_finiteHilbertProjection angularBasis (s j)).comp hU).sub hU).norm.pow 2)).aestronglyMeasurable.restrict)
  have hbound (j : J) (t : ℝ) : ‖error j t‖ ≤ major t := by
    dsimp only [error, major]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    calc
      _ ≤ Real.exp (-2 * t) * (4 * ‖U t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (finiteHilbertProjection_sub_norm_sq_le angularBasis (s j) (U t)) (Real.exp_pos _).le
      _ = _ := by ring
  have herrorI (j : J) : Integrable (error j) (volume.restrict (Ioi 0)) :=
    hmajor.mono' (herrorm j) (Eventually.of_forall (hbound j))
  have hlim : Tendsto (fun j => ∫ t in Ioi (0 : ℝ), error j t) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ))) (l := l) major
      (F := error) (f := fun _ => (0 : ℝ))
      (Eventually.of_forall herrorm)
      (Eventually.of_forall fun j => Eventually.of_forall (hbound j)) hmajor
      (Eventually.of_forall fun t => by
        have hp := ((finiteHilbertProjection_tendsto_filter angularBasis hs (U t)).sub
          (tendsto_const_nhds (x := U t))).norm.pow 2
        simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
          using hp.const_mul (Real.exp (-2 * t)))
    simpa only [integral_zero] using h
  apply hlim.congr'
  exact Eventually.of_forall fun j => by
    have he := (native_halfEnd_lift_memLp_of_weighted_integrable
      ((continuous_projectedAngular (s j) hU).measurable.sub hw)
      (projectedAngular_sub_ae (s j) U hae) (herrorI j)).2
    change (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
      cylinderLift (fun p => projectedAngular (s j) U p - w p) x ^ 2) = _ at he
    rw [cylinderLift_sub] at he
    exact he.symm

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- Every original finite physical field is genuinely L2 on the whole
punctured unit ball, with its bound produced by the original inverse. -/
theorem native_forced_halfEnd_finite_value_memLp
    (F : ℝ≥0 →ᵇ AngularL2) (s : Finset AngularIndex) :
    MemLp (cylinderLift (projectedAngular s
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) := by
  have hU := nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F
  apply (native_halfEnd_lift_memLp_of_expNegTwo_bound
    ((continuous_finiteHilbertProjection angularBasis s).comp hU)
    (continuous_projectedAngular s hU).measurable (projectedAngular_ae s _)
    ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖) ?_).1
  intro t _ht
  exact (finiteHilbertProjection_norm_le angularBasis s _).trans
    (nativeHalfHighDirichletPhysical_norm_le hκ0 hκ1 V hV hV0 F t)

/-- The actual native solution, with one fixed original representative,
is the global physical L2 limit of its original finite spectral fields. -/
theorem native_forced_halfEnd_global_value_projection_tendsto
    {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
    (F : ℝ≥0 →ᵇ AngularL2) {s : J → Finset AngularIndex} (hs : Tendsto s l atTop)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ)) :
    Tendsto (fun j => ∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
      (cylinderLift (projectedAngular (s j)
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)) x - cylinderLift w x) ^ 2)
      l (𝓝 0) := by
  have hU := nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F
  apply native_halfEnd_global_projection_error_tendsto hs hU hw hwAE
  apply native_halfEnd_weighted_norm_integrable_of_bound hU
    ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖)
  intro t ht
  have hC : 0 ≤ (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖ := by positivity
  exact (nativeHalfHighDirichletPhysical_norm_le hκ0 hκ1 V hV hV0 F t).trans
    (mul_le_of_le_one_left hC (Real.exp_le_one_iff.mpr (by linarith)))

/-- The same original high projected source converges globally in its
physical L2 norm, preserving the exact factor 64 in square errors. -/
theorem native_forced_halfEnd_global_source_projection_tendsto
    {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
    (F : ℝ≥0 →ᵇ AngularL2) {s : J → Finset AngularIndex} (hs : Tendsto s l atTop)
    {z : ℝ × S → ℝ} (hz : Measurable z)
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ)) :
    Tendsto (fun j => ∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
      (physicalForcing (fun p => Real.exp (-2 * p.1) *
        projectedAngular (s j) (fun t => nativeHighProjection (F t.toNNReal)) p) x -
        physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x) ^ 2) l (𝓝 0) := by
  have hH : Continuous (fun t : ℝ => nativeHighProjection (F t.toNNReal)) :=
    nativeHighProjection.continuous.comp (F.continuous.comp continuous_real_toNNReal)
  have htime := native_halfEnd_weighted_norm_integrable_of_bound hH ‖F‖
    (fun t _ht => (nativeAngularProjection_apply_norm_le _ (F t.toNNReal)).trans
      (F.norm_coe_le_norm t.toNNReal))
  have h := (native_halfEnd_global_projection_error_tendsto hs hH hz hzAE htime).const_mul (64 : ℝ)
  simpa only [integral_physicalForcing_expNegTwo_sq_sub, mul_zero] using h

#print axioms native_halfEnd_weighted_norm_integrable_of_bound
#print axioms native_halfEnd_global_projection_error_tendsto
#print axioms native_forced_halfEnd_finite_value_memLp
#print axioms native_forced_halfEnd_global_value_projection_tendsto
#print axioms native_forced_halfEnd_global_source_projection_tendsto

end Yamabe3.Analysis.SpherePolar
