import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndGlobalGradient
import Yamabe3.Analysis.UniformElliptic.NativeH1EquationLimit

/-!
# The original forced half-end satisfies its global physical weak equation

The actual full finite spectral net supplies global L2 convergence of
the original value and source and a global Cauchy estimate for its actual
Euclidean gradients.  The C1 closure theorem therefore constructs weak
partials of the same fixed physical representative, preserves strong H1
convergence and the total gradient energy, and passes the finite weak
equations to the limit on the entire punctured unit ball.

The singular potential is used only through its L2 product with each
actual compact test.  No global bound for the potential, no physical H1
membership, no gradient limit, and no finite PDE are supplied as inputs.
The original physical forcing retains its factor eight and its original
high projected source.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The actual full finite spectral net converges strongly in global
physical H1 to the same original representative. Its actual weak
gradient, total gradient energy and original normalized weak equation
are produced together on the whole punctured unit ball. -/
theorem native_forced_halfEnd_global_strong_equation
    (F : ℝ≥0 →ᵇ AngularL2) {w z : ℝ × S → ℝ}
    (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ)) :
    let u := cylinderLift w
    let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
    let uFin := fun s : Finset AngularIndex => cylinderLift (projectedAngular s
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    Poincare.Analysis.Sobolev.Weak.MemH1 u O ∧
    ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict O),
      (∀ i, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (du i) u O) ∧
      Tendsto (fun s : Finset AngularIndex => ∫ x in O,
        (uFin s x - u x) ^ 2 + ∑ i : Fin 3,
          (fderiv ℝ (uFin s) x (EuclideanSpace.single i 1) - du i x) ^ 2)
        atTop (𝓝 0) ∧
      Tendsto (fun s : Finset AngularIndex => ∫ x in O, ∑ i : Fin 3,
        (fderiv ℝ (uFin s) x (EuclideanSpace.single i 1)) ^ 2)
        atTop (𝓝 (∫ x in O, ∑ i : Fin 3, du i x ^ 2)) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ i : Fin 3, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          (∫ x in O, f x * φ x) / 8 +
            ∫ x in O, u x * (nativeHalfEndPotentialCoefficient V x * φ x)) := by
  classical
  letI : Countable AngularIndex := countable_angularIndex_for_halfEnd
  let U := nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F
  let H : ℝ → AngularL2 := fun t => nativeHighProjection (F t.toNNReal)
  let u := cylinderLift w
  let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
  let uFin := fun s : Finset AngularIndex => cylinderLift (projectedAngular s U)
  let fFin := fun s : Finset AngularIndex => physicalForcing
    (fun p : ℝ × S => Real.exp (-2 * p.1) * projectedAngular s H p)
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have hH : Continuous H := nativeHighProjection.continuous.comp
    (F.continuous.comp continuous_real_toNNReal)
  have hu : MemLp u 2 (volume.restrict O) :=
    (native_forced_halfEnd_value_global_memLp hκ0 hκ1 V hV hV0 F hw hwAE).1
  have hf : MemLp f 2 (volume.restrict O) :=
    (native_forced_halfEnd_source_global_memLp F hz hzAE).1
  have hC1 (s : Finset AngularIndex) : ContDiffOn ℝ 1 (uFin s) O :=
    (native_forced_halfEnd_finite_lift_contDiffOn_two hκ0 hκ1 V hV hV0 F s).of_le
      (by norm_num)
  have hval (s : Finset AngularIndex) : MemLp (uFin s) 2 (volume.restrict O) :=
    native_forced_halfEnd_finite_value_memLp hκ0 hκ1 V hV hV0 F s
  have hsource (s : Finset AngularIndex) : MemLp (fFin s) 2 (volume.restrict O) := by
    apply (native_halfEnd_physicalForcing_memLp
      ((continuous_finiteHilbertProjection angularBasis s).comp hH)
      (continuous_projectedAngular s hH).measurable (projectedAngular_ae s H)
      (B := ‖F‖) ?_).1
    intro t _ht
    exact (finiteHilbertProjection_norm_le angularBasis s (H t)).trans
      ((nativeAngularProjection_apply_norm_le (fun i => 6 ≤ angularEigenvalue i)
        (F t.toNNReal)).trans (F.norm_coe_le_norm _))
  have hder (s : Finset AngularIndex) (i : Fin 3) :
      MemLp (fun x => fderiv ℝ (uFin s) x (EuclideanSpace.single i 1)) 2
        (volume.restrict O) :=
    native_forced_halfEnd_finite_gradient_memLp hκ0 hκ1 V hV hV0 F s i
  have hlimu : Tendsto (fun s : Finset AngularIndex =>
      ∫ x in O, (uFin s x - u x) ^ 2) atTop (𝓝 0) :=
    native_forced_halfEnd_global_value_projection_tendsto
      (J := Finset AngularIndex) hκ0 hκ1 V hV hV0 F (s := id) tendsto_id hw hwAE
  have hlimf : Tendsto (fun s : Finset AngularIndex =>
      ∫ x in O, (fFin s x - f x) ^ 2) atTop (𝓝 0) :=
    native_forced_halfEnd_global_source_projection_tendsto
      (J := Finset AngularIndex) F (s := id) tendsto_id hz hzAE
  have hCtest (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ O) :
      MemLp (fun x => nativeHalfEndPotentialCoefficient V x * φ x) 2
        (volume.restrict O) := by
    have hzero : (0 : E) ∉ tsupport φ := fun h => (hs h).2 (by simp)
    exact (nativeHalfEndPotentialCoefficient_mul_test_memLp
      V hφ.continuous hc hzero).restrict O
  have heq (s : Finset AngularIndex) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
      (∫ x in O, ∑ i : Fin 3,
        fderiv ℝ (uFin s) x (EuclideanSpace.single i 1) *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        (∫ x in O, fFin s x * φ x) / 8 +
          ∫ x in O, uFin s x * (nativeHalfEndPotentialCoefficient V x * φ x) := by
    have hφLp : MemLp φ 2 (volume.restrict O) :=
      (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
    have hsrc : Integrable (fun x => fFin s x * φ x) (volume.restrict O) :=
      (hsource s).integrable_mul hφLp
    have hpot : Integrable (fun x => uFin s x *
        (nativeHalfEndPotentialCoefficient V x * φ x)) (volume.restrict O) :=
      (hval s).integrable_mul (hCtest φ hφ hc hs)
    calc
      _ = ∫ x in O, (fFin s x / 8 +
          nativeHalfEndPotentialCoefficient V x * uFin s x) * φ x :=
        native_forced_halfEnd_finite_weak_equation hκ0 hκ1 V hV hV0 F s φ hφ hc hs
      _ = ∫ x in O, (fFin s x * φ x) / 8 +
          uFin s x * (nativeHalfEndPotentialCoefficient V x * φ x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by
        rw [integral_add (hsrc.div_const _) hpot, integral_div]
  exact native_C1_same_value_weak_equation_limit
    (C := nativeHalfEndPotentialCoefficient V) hO hu hf uFin fFin hC1 hval hsource hder
    hlimu hlimf (native_forced_halfEnd_finite_gradient_pair_tendsto hκ0 hκ1 V hV hV0 F)
    hCtest heq

/-- Two actual joint representatives are selected once. The whole
finite-set net then converges to that same physical function in global
H1, preserves its actual gradient energy, and produces its weak equation
with that same original physical source. -/
theorem exists_native_forced_halfEnd_global_strong_equation_finset
    (F : ℝ≥0 →ᵇ AngularL2) :
    ∃ w z : ℝ × S → ℝ,
      Measurable w ∧ Measurable z ∧
      (∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ)) ∧
      (∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
        (nativeHighProjection (F t.toNNReal) : S → ℝ)) ∧
      let u := cylinderLift w
      let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
      let uFin := fun s : Finset AngularIndex => cylinderLift (projectedAngular s
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
      let O := Metric.ball (0 : E) 1 \ {(0 : E)}
      Poincare.Analysis.Sobolev.Weak.MemH1 u O ∧
      ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict O),
        (∀ i, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (du i) u O) ∧
        Tendsto (fun s : Finset AngularIndex => ∫ x in O,
          (uFin s x - u x) ^ 2 + ∑ i : Fin 3,
            (fderiv ℝ (uFin s) x (EuclideanSpace.single i 1) - du i x) ^ 2)
          atTop (𝓝 0) ∧
        Tendsto (fun s : Finset AngularIndex => ∫ x in O, ∑ i : Fin 3,
          (fderiv ℝ (uFin s) x (EuclideanSpace.single i 1)) ^ 2)
          atTop (𝓝 (∫ x in O, ∑ i : Fin 3, du i x ^ 2)) ∧
        (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
          (∫ x in O, ∑ i : Fin 3, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
            (∫ x in O, f x * φ x) / 8 +
              ∫ x in O, u x * (nativeHalfEndPotentialCoefficient V x * φ x)) := by
  classical
  have hU := nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F
  have hH : Continuous (fun t : ℝ => nativeHighProjection (F t.toNNReal)) :=
    nativeHighProjection.continuous.comp (F.continuous.comp continuous_real_toNNReal)
  obtain ⟨w, hwm, hw⟩ := exists_joint_L2_representative_of_continuous hU
  obtain ⟨z, hzm, hz⟩ := exists_joint_L2_representative_of_continuous hH
  have hwAE (t : ℝ) : (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ) := by
    simpa only [Measure.restrict_univ] using hw t
  have hzAE (t : ℝ) : (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ) := by
    simpa only [Measure.restrict_univ] using hz t
  exact ⟨w, z, hwm.measurable, hzm.measurable, hwAE, hzAE,
    native_forced_halfEnd_global_strong_equation hκ0 hκ1 V hV hV0 F
      hwm.measurable hzm.measurable hwAE hzAE⟩

#check @native_forced_halfEnd_global_strong_equation
#check @exists_native_forced_halfEnd_global_strong_equation_finset
#print axioms native_forced_halfEnd_global_strong_equation
#print axioms exists_native_forced_halfEnd_global_strong_equation_finset

end Yamabe3.Analysis.SpherePolar
