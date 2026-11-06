import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndFiniteWeakEquation
import Yamabe3.Analysis.Cylinder.NativeContinuousAngularFilterApproximation
import Yamabe3.Analysis.UniformElliptic.NativeLocalStrongEquation
import PoincareLib.Analysis.Parabolic.Dirichlet.SpectralCompactness

/-!
# Same-function local strong H1 for the constructed forced half-end

The original native Dirichlet construction supplies every finite C2
physical field and its actual weak equation.  Continuous angular
approximation supplies the actual L2 value and source limits along the
original cofinal family. The source keeps its physical coefficient eight.
The previously proved Caccioppoli argument then produces strong local
gradient convergence, the actual weak derivatives, convergence of the
total gradient energy, and the same original physical weak equation.

All cutoffs and potential bounds are produced on the actual nested
positive-time annuli.  No gradient-Cauchy, finite weak PDE, arbitrary
Sobolev representative, or normal boundary condition is an input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Manifold ContDiff Topology RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.NirenbergEuclidean

theorem closure_positive_cylinderAnnulus_subset_halfEnd {a b : ℝ} (ha : 0 < a) :
    closure (cylinderAnnulus a b) ⊆ Metric.ball (0 : E) 1 \ {(0 : E)} := by
  intro x hx
  have h := closure_cylinderAnnulus_subset_shell a b hx
  refine ⟨?_, ?_⟩
  · simp only [Metric.mem_ball, dist_zero_right]
    exact h.2.trans_lt (by simpa only [Real.exp_zero] using
      (Real.exp_lt_exp.mpr (neg_neg_of_pos ha)))
  · simpa only [mem_singleton_iff] using cylinderShell_ne_zero h

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The actual constructed half-end, its actual high source and their
fixed joint representatives satisfy the same strong local H1/PDE limit.
The geometric cutoff and bounded potential are proved inside this theorem. -/
theorem native_forced_halfEnd_local_strong_equation
    {J : Type*} [Nonempty J] [SemilatticeSup J]
    [(atTop : Filter J).IsCountablyGenerated]
    (F : ℝ≥0 →ᵇ AngularL2) {s : J → Finset AngularIndex} (hs : Tendsto s atTop atTop)
    {w z : ℝ × S → ℝ} (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ))
    {a b a' b' : ℝ} (ha : 0 < a) (haa' : a < a') (hb'b : b' < b) :
    let u := cylinderLift w
    let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
    let uSeq := fun n => cylinderLift (projectedAngular (s n)
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
    let W := cylinderAnnulus a' b'
    Poincare.Analysis.Sobolev.Weak.MemH1 u W ∧
    ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict W),
      (∀ i, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (du i) u W) ∧
      Tendsto (fun n => ∫ x in W, (uSeq n x - u x) ^ 2 + ∑ i : Fin 3,
        (fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1) - du i x) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in W, ∑ i : Fin 3,
        (fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1)) ^ 2)
        atTop (𝓝 (∫ x in W, ∑ i : Fin 3, du i x ^ 2)) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
        (∫ x in W, ∑ i : Fin 3, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          (∫ x in W, f x * φ x) / 8 +
            ∫ x in W, u x * (nativeHalfEndPotentialCoefficient V x * φ x)) := by
  let U := nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F
  let H : ℝ → AngularL2 := fun t => nativeHighProjection (F t.toNNReal)
  let u := cylinderLift w
  let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
  let uSeq : J → E → ℝ := fun n => cylinderLift (projectedAngular (s n) U)
  let fSeq : J → E → ℝ := fun n => physicalForcing
    (fun p : ℝ × S => Real.exp (-2 * p.1) * projectedAngular (s n) H p)
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let Ω := cylinderAnnulus a b
  let W := cylinderAnnulus a' b'
  let K := cylinderShell a b
  have hU : Continuous U := nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F
  have hH : Continuous H := nativeHighProjection.continuous.comp
    (F.continuous.comp continuous_real_toNNReal)
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have hΩ : IsOpen Ω := isOpen_cylinderAnnulus a b
  have hΩc : IsCompact (closure Ω) := isCompact_closure_cylinderAnnulus a b
  have hΩO : closure Ω ⊆ O := closure_positive_cylinderAnnulus_subset_halfEnd ha
  have hW : IsOpen W := isOpen_cylinderAnnulus a' b'
  have hWc : IsCompact (closure W) := isCompact_closure_cylinderAnnulus a' b'
  have hWΩc : closure W ⊆ Ω := closure_cylinderAnnulus_subset_wider haa' hb'b
  have hWΩ : W ⊆ Ω := subset_closure.trans hWΩc
  have hΩK : Ω ⊆ K := cylinderAnnulus_subset_shell a b
  have hμ : volume.restrict Ω ≤ volume.restrict K := Measure.restrict_mono hΩK le_rfl
  obtain ⟨η, hη, hηc, hηrange, hηone, hηΩ, B, hB, hDη⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound hWc hΩ hWΩc
  have hDηcoord (x : E) (i : Fin 3) :
      |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ B := by
    have h := (fderiv ℝ η x).le_opNorm (EuclideanSpace.single i 1)
    simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]
      using h.trans (by simpa using hDη x)
  have hQ : AEStronglyMeasurable (nativeHalfEndPotentialCoefficient V) (volume.restrict Ω) :=
    (nativeHalfEndPotentialCoefficient_measurable V).aestronglyMeasurable
  have hQbound : ∀ᵐ x ∂(volume.restrict Ω),
      ‖nativeHalfEndPotentialCoefficient V x‖ ≤ ‖V‖ / Real.exp (-b) ^ 2 := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact nativeHalfEndPotentialCoefficient_norm_le_on_shell V (hΩK hx)
  have huK : MemLp u 2 (volume.restrict K) := memLp_continuous_angular_lift hU hw hwAE a b
  have hfK : MemLp f 2 (volume.restrict K) :=
    memLp_halfEnd_physicalForcing_on_shell hH hz hzAE a b
  have huSeqK (n : J) : MemLp (uSeq n) 2 (volume.restrict K) :=
    memLp_projectedAngular_lift_of_continuous (s n) hU a b
  have hfSeqK (n : J) : MemLp (fSeq n) 2 (volume.restrict K) :=
    memLp_projected_halfEnd_physicalForcing_on_shell (s n) hH a b
  have hlimuK : Tendsto (fun n => ∫ x in K, (uSeq n x - u x) ^ 2) atTop (𝓝 0) :=
    integral_projectedAngular_lift_error_tendsto_filter hs hU hw hwAE a b
  have hlimfK : Tendsto (fun n => ∫ x in K, (fSeq n x - f x) ^ 2) atTop (𝓝 0) :=
    integral_projected_halfEnd_physicalForcing_error_tendsto_filter hs hH hz hzAE a b
  have hC1 (n : J) : ContDiffOn ℝ 1 (uSeq n) O :=
    (native_forced_halfEnd_finite_lift_contDiffOn_two hκ0 hκ1 V hV hV0 F (s n)).of_le
      (by norm_num)
  have heq (n : J) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
      (hsupp : tsupport φ ⊆ Ω) :
      (∫ x in Ω, ∑ i : Fin 3,
        fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1) *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in Ω, (fSeq n x / 8 + nativeHalfEndPotentialCoefficient V x * uSeq n x) * φ x :=
    native_forced_halfEnd_finite_weak_equation_on_open hκ0 hκ1 V hV hV0 F (s n)
      hΩ (subset_closure.trans hΩO) φ hφ hc hsupp
  exact native_C1_local_strong_equation_on_precompact
    hO hΩ hΩc hΩO hW hWΩ hη hηc hηΩ
    (fun x => hηrange ⟨x, rfl⟩) (fun x hx => hηone x (subset_closure hx))
    hB hDηcoord hQ hQbound (huK.mono_measure hμ) (hfK.mono_measure hμ)
    uSeq fSeq hC1 (fun n => (hfSeqK n).mono_measure hμ)
    (native_tendsto_integral_sq_sub_restrict hΩK huSeqK huK hlimuK)
    (native_tendsto_integral_sq_sub_restrict hΩK hfSeqK hfK hlimfK) heq

/-- One actual exhaustion and two actual joint representatives are
chosen once, before every pair of local annuli.  The resulting physical
function and physical source are therefore the same throughout. -/
theorem exists_native_forced_halfEnd_local_strong_equation
    (F : ℝ≥0 →ᵇ AngularL2) :
    ∃ (s : ℕ → Finset AngularIndex) (w z : ℝ × S → ℝ),
      Monotone s ∧ Tendsto s atTop atTop ∧ Measurable w ∧ Measurable z ∧
      (∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ)) ∧
      (∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
        (nativeHighProjection (F t.toNNReal) : S → ℝ)) ∧
      ∀ (a b a' b' : ℝ), 0 < a → a < a' → b' < b →
        let u := cylinderLift w
        let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
        let uSeq := fun n => cylinderLift (projectedAngular (s n)
          (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
        let W := cylinderAnnulus a' b'
        Poincare.Analysis.Sobolev.Weak.MemH1 u W ∧
        ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict W),
          (∀ i, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (du i) u W) ∧
          Tendsto (fun n => ∫ x in W, (uSeq n x - u x) ^ 2 + ∑ i : Fin 3,
            (fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1) - du i x) ^ 2) atTop (𝓝 0) ∧
          Tendsto (fun n => ∫ x in W, ∑ i : Fin 3,
            (fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1)) ^ 2)
            atTop (𝓝 (∫ x in W, ∑ i : Fin 3, du i x ^ 2)) ∧
          (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
            (∫ x in W, ∑ i : Fin 3, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
              (∫ x in W, f x * φ x) / 8 +
                ∫ x in W, u x * (nativeHalfEndPotentialCoefficient V x * φ x)) := by
  letI : Countable AngularIndex :=
    Poincare.Analysis.Dirichlet.CompactSpectral.countable_basisIndex
      (PoincareMT.LeviCivitaData.Dirichlet.domainL2Resolvent sphereD univ)
      (PoincareMT.LeviCivitaData.Dirichlet.isCompactOperator_domainL2Resolvent
        sphereD univ (by decide) isOpen_univ
        (by simpa using (isCompact_univ : IsCompact (univ : Set S))))
      PoincareMT.LeviCivitaData.Dirichlet.domainL2Resolvent_isSelfAdjoint
  obtain ⟨s, hsmono, hs⟩ := exists_finite_basis_exhaustion (ι := AngularIndex)
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
  exact ⟨s, w, z, hsmono, hs, hwm.measurable, hzm.measurable, hwAE, hzAE,
    fun _ _ _ _ ha haa' hb'b => native_forced_halfEnd_local_strong_equation
      hκ0 hκ1 V hV hV0 F hs hwm.measurable hzm.measurable hwAE hzAE ha haa' hb'b⟩

/-- The actual compact-resolvent spectrum makes the full Finset filter
countably generated. This is proved for the native angular index. -/
theorem countable_angularIndex_for_halfEnd : Countable AngularIndex :=
  Poincare.Analysis.Dirichlet.CompactSpectral.countable_basisIndex
    (PoincareMT.LeviCivitaData.Dirichlet.domainL2Resolvent sphereD univ)
    (PoincareMT.LeviCivitaData.Dirichlet.isCompactOperator_domainL2Resolvent
      sphereD univ (by decide) isOpen_univ
      (by simpa using (isCompact_univ : IsCompact (univ : Set S))))
    PoincareMT.LeviCivitaData.Dirichlet.domainL2Resolvent_isSelfAdjoint

/-- The actual full finite-set net, with representatives chosen once
before all annuli, converges strongly in local H1 to the same physical
function and gives its original weak equation and gradient energy. -/
theorem exists_native_forced_halfEnd_local_strong_equation_finset
    (F : ℝ≥0 →ᵇ AngularL2) :
    ∃ w z : ℝ × S → ℝ,
      Measurable w ∧ Measurable z ∧
      (∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ)) ∧
      (∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
        (nativeHighProjection (F t.toNNReal) : S → ℝ)) ∧
      ∀ (a b a' b' : ℝ), 0 < a → a < a' → b' < b →
        let u := cylinderLift w
        let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
        let uFin := fun s : Finset AngularIndex => cylinderLift (projectedAngular s
          (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
        let W := cylinderAnnulus a' b'
        Poincare.Analysis.Sobolev.Weak.MemH1 u W ∧
        ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict W),
          (∀ i, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (du i) u W) ∧
          Tendsto (fun s : Finset AngularIndex => ∫ x in W,
            (uFin s x - u x) ^ 2 + ∑ i : Fin 3,
              (fderiv ℝ (uFin s) x (EuclideanSpace.single i 1) - du i x) ^ 2)
            atTop (𝓝 0) ∧
          Tendsto (fun s : Finset AngularIndex => ∫ x in W, ∑ i : Fin 3,
            (fderiv ℝ (uFin s) x (EuclideanSpace.single i 1)) ^ 2)
            atTop (𝓝 (∫ x in W, ∑ i : Fin 3, du i x ^ 2)) ∧
          (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
            (∫ x in W, ∑ i : Fin 3, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
              (∫ x in W, f x * φ x) / 8 +
                ∫ x in W, u x * (nativeHalfEndPotentialCoefficient V x * φ x)) := by
  classical
  letI : Countable AngularIndex := countable_angularIndex_for_halfEnd
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
  refine ⟨w, z, hwm.measurable, hzm.measurable, hwAE, hzAE, ?_⟩
  intro a b a' b' ha haa' hb'b
  exact native_forced_halfEnd_local_strong_equation (J := Finset AngularIndex)
    hκ0 hκ1 V hV hV0 F (s := id) tendsto_id
    hwm.measurable hzm.measurable hwAE hzAE ha haa' hb'b

#print axioms closure_positive_cylinderAnnulus_subset_halfEnd
#print axioms native_forced_halfEnd_local_strong_equation
#print axioms exists_native_forced_halfEnd_local_strong_equation
#print axioms countable_angularIndex_for_halfEnd
#print axioms exists_native_forced_halfEnd_local_strong_equation_finset

end Yamabe3.Analysis.SpherePolar
