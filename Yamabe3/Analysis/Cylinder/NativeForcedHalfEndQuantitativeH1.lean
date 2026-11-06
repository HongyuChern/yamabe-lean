import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndGlobalEquation

/-!
# Quantitative global H1 for the same forced half-end

The actual finite Euclidean gradients are first square integrable and
uniformly bounded.  The finite-pair estimate with the empty projection,
the two genuine Hilbert projection contractions, and the original full
time-energy estimate give the constant `(CE^2 + CD^2) / 2`.

The already proved global equation supplies one actual weak gradient of
the same physical representative, together with convergence of its total
gradient energy.  Passing the finite uniform bound through that actual
limit gives the bound for this same gradient.  Adding the original value
estimate gives `C0^2 / 6 + (CE^2 + CD^2) / 2` for the squared H1 energy.

The full finite-set strong convergence, the original source and its
factor eight, and the original weak equation are retained.  No gradient
convergence, gradient Cauchy estimate, or H1 membership is an input.
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

/-- Every original finite field has genuinely integrable Euclidean
gradient energy, bounded by the same source constant independently of
the finite set. -/
theorem native_forced_halfEnd_finite_gradient_energy_le
    (F : ℝ≥0 →ᵇ AngularL2) (s : Finset AngularIndex) :
    let u := cylinderLift (projectedAngular s
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    IntegrableOn (fun x : E =>
      ∑ j : Fin 3, (fderiv ℝ u x (EuclideanSpace.single j 1)) ^ 2) O ∧
    (∫ x in O, ∑ j : Fin 3,
      (fderiv ℝ u x (EuclideanSpace.single j 1)) ^ 2) ≤
      (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
        nativeHalfHighDirichletDerivativeBound κ V ^ 2) * ‖F‖ ^ 2 / 2 := by
  classical
  let u := cylinderLift (projectedAngular s
    (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let eCurve := nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F
  let dCurve := nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F
  let B : ℝ → ℝ := fun r =>
    ‖finiteHilbertProjection angularEnergyBasis s (eCurve r)‖ ^ 2 +
      ‖finiteHilbertProjection angularBasis s (dCurve r)‖ ^ 2
  let T : ℝ → ℝ := fun r => ‖eCurve r‖ ^ 2 + ‖dCurve r‖ ^ 2
  have hPE (a : AngularH1) : finiteHilbertProjection angularEnergyBasis ∅ a = 0 := by
    simp only [finiteHilbertProjection, Finset.sum_empty]
  have hPD (a : AngularL2) : finiteHilbertProjection angularBasis ∅ a = 0 := by
    simp only [finiteHilbertProjection, Finset.sum_empty]
  have hder (j : Fin 3) :
      MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single j 1)) 2 (volume.restrict O) :=
    native_forced_halfEnd_finite_gradient_memLp hκ0 hκ1 V hV hV0 F s j
  have hgradI : IntegrableOn (fun x : E =>
      ∑ j : Fin 3, (fderiv ℝ u x (EuclideanSpace.single j 1)) ^ 2) O :=
    integrable_finsetSum Finset.univ (fun j _ => (hder j).integrable_sq)
  have hBI : IntegrableOn B (Ici 0) := by
    simpa only [B, eCurve, dCurve, hPE, hPD, sub_zero] using
      nativeHalfHighDirichletPhysical_pair_energy_integrable hκ0 hκ1 V hV hV0 F s ∅
  have htime := nativeHalfHighDirichletPhysical_total_energy_le hκ0 hκ1 V hV hV0 F
  have hTI : IntegrableOn T (Ici 0) := htime.1
  have hpoint (r : ℝ) : B r ≤ T r := by
    dsimp only [B, T]
    exact add_le_add
      (pow_le_pow_left₀ (norm_nonneg _)
        (finiteHilbertProjection_norm_le angularEnergyBasis s (eCurve r)) 2)
      (pow_le_pow_left₀ (norm_nonneg _)
        (finiteHilbertProjection_norm_le angularBasis s (dCurve r)) 2)
  have hfinite : (∫ x in O, ∑ j : Fin 3,
      (fderiv ℝ u x (EuclideanSpace.single j 1)) ^ 2) ≤
        2 * ∫ r in Ici (0 : ℝ), B r := by
    simpa only [u, O, B, eCurve, dCurve, cylinderLift_projectedAngular_empty,
      fderiv_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply, hPE, hPD, sub_zero] using
      (native_forced_halfEnd_finite_gradient_pair_bound hκ0 hκ1 V hV hV0 F s ∅).2
  refine ⟨hgradI, ?_⟩
  calc
    _ ≤ 2 * ∫ r in Ici (0 : ℝ), B r := hfinite
    _ ≤ 2 * ∫ r in Ici (0 : ℝ), T r :=
      mul_le_mul_of_nonneg_left
        (setIntegral_mono_on hBI hTI measurableSet_Ici (fun r _hr => hpoint r))
        (by norm_num : (0 : ℝ) ≤ 2)
    _ ≤ 2 * ((nativeHalfHighDirichletEnergyBound κ V ^ 2 +
        nativeHalfHighDirichletDerivativeBound κ V ^ 2) * ‖F‖ ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left htime.2 (by norm_num : (0 : ℝ) ≤ 2)
    _ = _ := by ring

/-- The original global equation and full finite-set convergence are
retained with the very same weak gradient.  Its gradient energy and
total squared H1 energy are genuinely integrable and quantitatively
bounded by the original source. -/
theorem native_forced_halfEnd_global_quantitative_strong_equation
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
      (∀ j, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv j (du j) u O) ∧
      Tendsto (fun s : Finset AngularIndex => ∫ x in O,
        ((uFin s x - u x) ^ 2 + (∑ j : Fin 3,
          (fderiv ℝ (uFin s) x (EuclideanSpace.single j 1) - du j x) ^ 2)))
        atTop (𝓝 0) ∧
      Tendsto (fun s : Finset AngularIndex => ∫ x in O, ∑ j : Fin 3,
        (fderiv ℝ (uFin s) x (EuclideanSpace.single j 1)) ^ 2)
        atTop (𝓝 (∫ x in O, ∑ j : Fin 3, du j x ^ 2)) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ j : Fin 3, du j x * fderiv ℝ φ x (EuclideanSpace.single j 1)) =
          (∫ x in O, f x * φ x) / 8 +
            ∫ x in O, u x * (nativeHalfEndPotentialCoefficient V x * φ x)) ∧
      IntegrableOn (fun x : E => ∑ j : Fin 3, du j x ^ 2) O ∧
      (∫ x in O, ∑ j : Fin 3, du j x ^ 2) ≤
        (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
          nativeHalfHighDirichletDerivativeBound κ V ^ 2) * ‖F‖ ^ 2 / 2 ∧
      IntegrableOn (fun x : E => (u x ^ 2 + (∑ j : Fin 3, du j x ^ 2))) O ∧
      (∫ x in O, (u x ^ 2 + (∑ j : Fin 3, du j x ^ 2))) ≤
        ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 / 6 +
          (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
            nativeHalfHighDirichletDerivativeBound κ V ^ 2) / 2) * ‖F‖ ^ 2 := by
  classical
  let u := cylinderLift w
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  obtain ⟨hH1, du, hdu, hstrong, henergy, heq⟩ :=
    native_forced_halfEnd_global_strong_equation hκ0 hκ1 V hV hV0 F hw hz hwAE hzAE
  have hgradI : IntegrableOn (fun x : E => ∑ j : Fin 3, du j x ^ 2) O :=
    integrable_finsetSum Finset.univ (fun j _ => (Lp.memLp (du j)).integrable_sq)
  have hgradBound : (∫ x in O, ∑ j : Fin 3, du j x ^ 2) ≤
      (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
        nativeHalfHighDirichletDerivativeBound κ V ^ 2) * ‖F‖ ^ 2 / 2 :=
    le_of_tendsto' henergy (fun s =>
      (native_forced_halfEnd_finite_gradient_energy_le hκ0 hκ1 V hV hV0 F s).2)
  have hvalue := native_forced_halfEnd_value_global_memLp hκ0 hκ1 V hV hV0 F hw hwAE
  have hvalueI : IntegrableOn (fun x : E => u x ^ 2) O := hvalue.1.integrable_sq
  have htotalI : IntegrableOn (fun x : E => (u x ^ 2 + (∑ j : Fin 3, du j x ^ 2))) O :=
    hvalueI.add hgradI
  refine ⟨hH1, du, hdu, hstrong, henergy, heq, hgradI, hgradBound, htotalI, ?_⟩
  rw [integral_add hvalueI hgradI]
  calc
    _ ≤ (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 * ‖F‖ ^ 2 / 6 +
        (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
          nativeHalfHighDirichletDerivativeBound κ V ^ 2) * ‖F‖ ^ 2 / 2 :=
      add_le_add hvalue.2 hgradBound
    _ = _ := by ring

/-- Actual joint representatives of the original value and high source
are produced once.  The same physical value, source, weak gradient,
global equation and full finite-set strong limit carry the quantitative
global squared H1 bound. -/
theorem exists_native_forced_halfEnd_global_quantitative_strong_equation_finset
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
        (∀ j, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv j (du j) u O) ∧
        Tendsto (fun s : Finset AngularIndex => ∫ x in O,
          ((uFin s x - u x) ^ 2 + (∑ j : Fin 3,
            (fderiv ℝ (uFin s) x (EuclideanSpace.single j 1) - du j x) ^ 2)))
          atTop (𝓝 0) ∧
        Tendsto (fun s : Finset AngularIndex => ∫ x in O, ∑ j : Fin 3,
          (fderiv ℝ (uFin s) x (EuclideanSpace.single j 1)) ^ 2)
          atTop (𝓝 (∫ x in O, ∑ j : Fin 3, du j x ^ 2)) ∧
        (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
          (∫ x in O, ∑ j : Fin 3, du j x * fderiv ℝ φ x (EuclideanSpace.single j 1)) =
            (∫ x in O, f x * φ x) / 8 +
              ∫ x in O, u x * (nativeHalfEndPotentialCoefficient V x * φ x)) ∧
        IntegrableOn (fun x : E => ∑ j : Fin 3, du j x ^ 2) O ∧
        (∫ x in O, ∑ j : Fin 3, du j x ^ 2) ≤
          (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
            nativeHalfHighDirichletDerivativeBound κ V ^ 2) * ‖F‖ ^ 2 / 2 ∧
        IntegrableOn (fun x : E => (u x ^ 2 + (∑ j : Fin 3, du j x ^ 2))) O ∧
        (∫ x in O, (u x ^ 2 + (∑ j : Fin 3, du j x ^ 2))) ≤
          ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 / 6 +
            (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
              nativeHalfHighDirichletDerivativeBound κ V ^ 2) / 2) * ‖F‖ ^ 2 := by
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
    native_forced_halfEnd_global_quantitative_strong_equation hκ0 hκ1 V hV hV0 F
      hwm.measurable hzm.measurable hwAE hzAE⟩

#print axioms native_forced_halfEnd_finite_gradient_energy_le
#print axioms native_forced_halfEnd_global_quantitative_strong_equation
#print axioms exists_native_forced_halfEnd_global_quantitative_strong_equation_finset

end Yamabe3.Analysis.SpherePolar
