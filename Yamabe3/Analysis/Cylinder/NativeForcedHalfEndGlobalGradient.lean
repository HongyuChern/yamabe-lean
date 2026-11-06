import Yamabe3.Analysis.Cylinder.NativeFiniteC2GlobalEnergy
import Yamabe3.Analysis.Cylinder.NativeForcedFiniteDifferencePhysical
import Yamabe3.Analysis.Cylinder.NativeHalfEndGlobalProjection
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndStrongLimit

/-!
# The actual full finite spectral net has a global physical H1 limit

The genuine pointwise finite-difference identity is differentiated on the
punctured unit ball.  Its actual Euclidean gradient energy is computed by
the finite C2 polar theorem and controlled by the already constructed
angular H1 and strong-time-derivative energies.  Their real two-index
Cauchy estimate therefore supplies the missing physical gradient Cauchy
estimate on the entire domain.

Completeness and C1 integration by parts construct actual global weak
partials of the same original joint representative.  No gradient Cauchy
estimate, physical H1 membership, or derivative limit is assumed.
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

/-- The actual Euclidean gradient difference is L2 and its full-domain
energy is controlled by the original two-index Hilbert energy. -/
theorem native_forced_halfEnd_finite_gradient_pair_bound
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) :
    let u := fun a : Finset AngularIndex => cylinderLift (projectedAngular a
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    (∀ j : Fin 3, MemLp (fun x =>
      fderiv ℝ (u s) x (EuclideanSpace.single j 1) -
        fderiv ℝ (u t) x (EuclideanSpace.single j 1)) 2 (volume.restrict O)) ∧
    (∫ x in O, ∑ j : Fin 3,
      (fderiv ℝ (u s) x (EuclideanSpace.single j 1) -
        fderiv ℝ (u t) x (EuclideanSpace.single j 1)) ^ 2) ≤
      2 * ∫ r in Ici (0 : ℝ),
        ‖finiteHilbertProjection angularEnergyBasis s
            (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r) -
          finiteHilbertProjection angularEnergyBasis t
            (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)‖ ^ 2 +
        ‖finiteHilbertProjection angularBasis s
            (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) -
          finiteHilbertProjection angularBasis t
            (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r)‖ ^ 2 := by
  classical
  let U := nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F
  let u := fun a : Finset AngularIndex => cylinderLift (projectedAngular a U)
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let q := nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t
  let B : ℝ → ℝ := fun r =>
    ‖finiteHilbertProjection angularEnergyBasis s
        (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r) -
      finiteHilbertProjection angularEnergyBasis t
        (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)‖ ^ 2 +
    ‖finiteHilbertProjection angularBasis s
        (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) -
      finiteHilbertProjection angularBasis t
        (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r)‖ ^ 2
  have hO : MeasurableSet O := (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hq (i : AngularIndex) (_hi : i ∈ s ∪ t) : ContDiffOn ℝ 2 (q i) (Ioi 0) :=
    nativeHalfHighDirichletFiniteDifferenceCoefficient_c2 hκ0 hκ1 V hV hV0 F s t i
  have hB : IntegrableOn B (Ioi 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (f := B) (b := (0 : ℝ)) (by finiteness)).mp
    (nativeHalfHighDirichletPhysical_pair_energy_integrable hκ0 hκ1 V hV hV0 F s t)
  have hbound (r : ℝ) (hr : 0 < r) :
      (∑ i ∈ s ∪ t, ((deriv (q i) r + q i r / 2) ^ 2 +
        angularEigenvalue i * q i r ^ 2)) ≤ 2 * B r :=
    nativeHalfHighDirichletFiniteDifference_modal_energy_le hκ0 hκ1 V hV hV0 F s t r hr
  have htime := native_finitePhysical_coefficient_energy_integrable_of_bound
    (s ∪ t) q hq (hB.const_mul 2) hbound
  obtain ⟨hd, he⟩ := native_finitePhysical_global_gradient_energy (s ∪ t) q hq htime
  have hpartial (j : Fin 3) :
      (fun x => fderiv ℝ (finitePhysical (s ∪ t) q) x (EuclideanSpace.single j 1)) =ᵐ[volume.restrict O]
        (fun x => fderiv ℝ (u s) x (EuclideanSpace.single j 1) -
          fderiv ℝ (u t) x (EuclideanSpace.single j 1)) := by
    filter_upwards [ae_restrict_mem hO] with x hx
    exact native_forced_finiteDifference_partial_eq hκ0 hκ1 V hV hV0 F s t hx j
  have hsquare : (∫ x in O, ∑ j : Fin 3,
      (fderiv ℝ (u s) x (EuclideanSpace.single j 1) -
        fderiv ℝ (u t) x (EuclideanSpace.single j 1)) ^ 2) =
      ∫ x in O, ∑ j : Fin 3,
        (fderiv ℝ (finitePhysical (s ∪ t) q) x (EuclideanSpace.single j 1)) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hO] with x hx
    apply Finset.sum_congr rfl
    intro j hj
    rw [native_forced_finiteDifference_partial_eq hκ0 hκ1 V hV hV0 F s t hx j]
  refine ⟨fun j => (hd j).ae_eq (hpartial j), ?_⟩
  rw [hsquare, he]
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), 2 * B r :=
      setIntegral_mono_on htime (hB.const_mul 2) measurableSet_Ioi hbound
    _ = 2 * ∫ r in Ici (0 : ℝ), B r := by
      rw [integral_const_mul, integral_Ici_eq_integral_Ioi]

/-- Each actual finite field has all its original classical partials
in global L2. The empty finite set is the actual zero function. -/
theorem native_forced_halfEnd_finite_gradient_memLp
    (F : ℝ≥0 →ᵇ AngularL2) (s : Finset AngularIndex) (j : Fin 3) :
    MemLp (fun x => fderiv ℝ (cylinderLift (projectedAngular s
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))) x
        (EuclideanSpace.single j 1)) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) := by
  have h := (native_forced_halfEnd_finite_gradient_pair_bound hκ0 hκ1 V hV hV0 F s ∅).1 j
  simpa only [cylinderLift_projectedAngular_empty, fderiv_zero,
    Pi.zero_apply, ContinuousLinearMap.zero_apply, sub_zero] using h

/-- The actual full finite-set family is globally Cauchy in the real
Euclidean coordinate-gradient square integral. -/
theorem native_forced_halfEnd_finite_gradient_pair_tendsto
    (F : ℝ≥0 →ᵇ AngularL2) :
    let u := fun a : Finset AngularIndex => cylinderLift (projectedAngular a
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
    Tendsto (fun p : Finset AngularIndex × Finset AngularIndex =>
      ∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, ∑ j : Fin 3,
        (fderiv ℝ (u p.1) x (EuclideanSpace.single j 1) -
          fderiv ℝ (u p.2) x (EuclideanSpace.single j 1)) ^ 2) atTop (𝓝 0) := by
  have hlim := (nativeHalfHighDirichletPhysical_pair_energy_tendsto_finset
    hκ0 hκ1 V hV hV0 F).const_mul (2 : ℝ)
  simp only [mul_zero] at hlim
  exact squeeze_zero
    (fun p => integral_nonneg (fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
    (fun p => (native_forced_halfEnd_finite_gradient_pair_bound
      hκ0 hκ1 V hV hV0 F p.1 p.2).2) hlim

/-- Global physical H1 and actual strong convergence of the full finite
spectral net to the same original physical function, with weak partials
constructed by completeness and integration by parts. -/
theorem native_forced_halfEnd_global_strong_H1
    (F : ℝ≥0 →ᵇ AngularL2) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ)) :
    let uFin := fun s : Finset AngularIndex => cylinderLift (projectedAngular s
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    Poincare.Analysis.Sobolev.Weak.MemH1 (cylinderLift w) O ∧
    ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict O),
      (∀ j, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv j (du j) (cylinderLift w) O) ∧
      Tendsto (fun s : Finset AngularIndex => ∫ x in O,
        (uFin s x - cylinderLift w x) ^ 2 + ∑ j : Fin 3,
          (fderiv ℝ (uFin s) x (EuclideanSpace.single j 1) - du j x) ^ 2)
        atTop (𝓝 0) := by
  classical
  letI : Countable AngularIndex := countable_angularIndex_for_halfEnd
  let uFin := fun s : Finset AngularIndex => cylinderLift (projectedAngular s
    (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have hu : MemLp (cylinderLift w) 2 (volume.restrict O) :=
    (native_forced_halfEnd_value_global_memLp hκ0 hκ1 V hV hV0 F hw hwAE).1
  have hC1 (s : Finset AngularIndex) : ContDiffOn ℝ 1 (uFin s) O :=
    (native_forced_halfEnd_finite_lift_contDiffOn_two hκ0 hκ1 V hV hV0 F s).of_le
      (by norm_num)
  have hval (s : Finset AngularIndex) : MemLp (uFin s) 2 (volume.restrict O) :=
    native_forced_halfEnd_finite_value_memLp hκ0 hκ1 V hV hV0 F s
  have hder (s : Finset AngularIndex) (j : Fin 3) :
      MemLp (fun x => fderiv ℝ (uFin s) x (EuclideanSpace.single j 1)) 2 (volume.restrict O) :=
    native_forced_halfEnd_finite_gradient_memLp hκ0 hκ1 V hV hV0 F s j
  have hlim := native_forced_halfEnd_global_value_projection_tendsto
    (J := Finset AngularIndex) hκ0 hκ1 V hV hV0 F (s := id) tendsto_id hw hwAE
  obtain ⟨hH1, du, hdu, _, hstrong⟩ :=
    native_exists_strong_weak_partials_of_C1_cauchy hO hu uFin hC1 hval hder hlim
      (native_forced_halfEnd_finite_gradient_pair_tendsto hκ0 hκ1 V hV hV0 F)
  exact ⟨hH1, du, hdu, hstrong⟩

#print axioms native_forced_halfEnd_finite_gradient_pair_bound
#print axioms native_forced_halfEnd_finite_gradient_memLp
#print axioms native_forced_halfEnd_finite_gradient_pair_tendsto
#print axioms native_forced_halfEnd_global_strong_H1

end Yamabe3.Analysis.SpherePolar
