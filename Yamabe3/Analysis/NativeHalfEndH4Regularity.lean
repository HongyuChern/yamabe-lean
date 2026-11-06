import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndLocalH2
import Yamabe3.Analysis.UniformElliptic.InhomogeneousBootstrap

/-!
# The same actual half-end solution gains two derivatives from its H2 source

The weak solution and its first derivatives are produced by the original
Dirichlet construction.  The source regularity is a property of the
specified physical high source, not a new solution hypothesis.  Both
bootstrap steps concern the identical representative.  The conclusion is
interior local H4; no boundary estimate or uniform graph norm is claimed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal ContDiff Topology RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration

/-- Two genuine applications of the weak gain-of-two theorem.  The zeroth
order coefficient multiplies the already constructed solution; it is not
silently included in the H2 source assumption. -/
theorem memWkpLocally_four_of_weak_H2_source {d : ℕ} [NeZero d]
    {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O)
    {A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {Q F u : EuclideanSpace ℝ (Fin d) → ℝ}
    {p : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hpos : ∀ x ∈ O, (A x).PosDef) (hQ : ContDiff ℝ ∞ Q)
    (hF : MemWkpLocally 2 F O)
    (hu : MemLp u 2 (volume.restrict O))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (heq : WeakEquation O (matrixFlux A p) (fun x => F x + Q x * u x)) :
    MemWkpLocally 4 u O := by
  have hu0 : MemWkpLocally 0 u O := locally_of_memWkp hO hu
  have hu2 : MemWkpLocally 2 u O :=
    memWkpLocally_add_two_of_weakEquation 0 hO hA hpos hu hp hpartial
      ((hF.mono_order (by omega)).add (hu0.smooth_mul hQ)) heq
  exact memWkpLocally_add_two_of_weakEquation 2 hO hA hpos hu hp hpartial
    (hF.add (hu2.smooth_mul hQ)) heq

/-- The coefficient need only be smooth near the closure of the current
domain.  An actual smooth extension is constructed and used on that domain. -/
theorem memWkpLocally_four_of_local_potential_H2_source {d : ℕ} [NeZero d]
    {O W : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O) (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (hWO : closure W ⊆ O)
    {A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {Q F u : EuclideanSpace ℝ (Fin d) → ℝ}
    {p : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hpos : ∀ x ∈ W, (A x).PosDef) (hQ : ContDiffOn ℝ ∞ Q O)
    (hF : MemWkpLocally 2 F W)
    (hu : MemLp u 2 (volume.restrict W))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict W))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u W)
    (heq : WeakEquation W (matrixFlux A p) (fun x => F x + Q x * u x)) :
    MemWkpLocally 4 u W := by
  obtain ⟨Qe, hQe, -, hQeg⟩ :=
    exists_smooth_compact_extension_near_compact hO hWc hWO hQ
  apply memWkpLocally_four_of_weak_H2_source hW hA hpos hQe hF hu hp hpartial
  intro φ hφ hc hs
  calc
    _ = ∫ x in W, (F x + Q x * u x) * φ x := heq φ hφ hc hs
    _ = ∫ x in W, (F x + Qe x * u x) * φ x := by
      apply setIntegral_congr_fun hW.measurableSet
      intro x hx
      dsimp only
      rw [(hQeg x (subset_closure hx)).self_of_nhds]

end Yamabe3.Analysis.UniformElliptic

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration

theorem nativeHalfEndPotentialCoefficient_contDiffOn (V : ℝ →ᵇ ℝ)
    (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t)) :
    ContDiffOn ℝ ∞ (nativeHalfEndPotentialCoefficient V) ({0}ᶜ : Set E) := by
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx0
  have hl := ((Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr hx0)).comp x hn).neg
  exact ((hVs.contDiffAt.comp x hl).div (hn.pow 2)
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0))).contDiffWithinAt

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The actual zero-entrance half-end has local H4 on every positive
annulus when its same physical high source has local H2.  In particular
neither a weak equation nor H2 membership of the solution is an input. -/
theorem native_forced_halfEnd_local_H4_on_annulus
    (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t))
    (F : ℝ≥0 →ᵇ AngularL2) {w z : ℝ × S → ℝ}
    (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ))
    {a b : ℝ} (ha : 0 < a)
    (hf2 : MemWkpLocally 2
      (physicalForcing (fun q : ℝ × S => Real.exp (-2 * q.1) * z q))
      (cylinderAnnulus a b)) :
    MemWkpLocally 4 (cylinderLift w) (cylinderAnnulus a b) := by
  classical
  letI : Countable AngularIndex := countable_angularIndex_for_halfEnd
  obtain ⟨hH1, p, hpartial, -, -, heq⟩ :=
    native_forced_halfEnd_local_strong_equation (J := Finset AngularIndex)
      hκ0 hκ1 V hV hV0 F (s := id) tendsto_id
      hw hz hwAE hzAE (a := a / 2) (b := b + 1) (a' := a) (b' := b)
      (by linarith) (by linarith) (by linarith)
  let W := cylinderAnnulus a b
  let u := cylinderLift w
  let f := physicalForcing (fun q : ℝ × S => Real.exp (-2 * q.1) * z q)
  let Q := nativeHalfEndPotentialCoefficient V
  have hW : IsOpen W := isOpen_cylinderAnnulus a b
  have hH : Continuous (fun t : ℝ => nativeHighProjection (F t.toNNReal)) :=
    nativeHighProjection.continuous.comp (F.continuous.comp continuous_real_toNNReal)
  have hf : MemLp f 2 (volume.restrict W) :=
    (memLp_halfEnd_physicalForcing_on_shell hH hz hzAE a b).mono_measure
      (Measure.restrict_mono (cylinderAnnulus_subset_shell a b) le_rfl)
  have hu : MemLp u 2 (volume.restrict W) := hH1.1
  have hQu : MemLp (fun x => Q x * u x) 2 (volume.restrict W) := by
    apply hu.of_le_mul (c := ‖V‖ / Real.exp (-b) ^ 2)
      ((nativeHalfEndPotentialCoefficient_measurable V).aestronglyMeasurable.mul
        hu.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
    change ‖nativeHalfEndPotentialCoefficient V x * u x‖ ≤
      (‖V‖ / Real.exp (-b) ^ 2) * ‖u x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (nativeHalfEndPotentialCoefficient_norm_le_on_shell V
        (cylinderAnnulus_subset_shell a b hx)) (norm_nonneg (u x))
  have hweak : WeakEquation W
      (matrixFlux (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun i => (p i : E → ℝ)))
      (fun x => f x / 8 + Q x * u x) := by
    intro φ hφ hc hs
    have hφL : MemLp φ 2 (volume.restrict W) :=
      (hφ.continuous.memLp_of_hasCompactSupport hc).restrict W
    have hsrc := hf.integrable_mul hφL
    have hpot := hQu.integrable_mul hφL
    change Integrable (fun x => f x * φ x) (volume.restrict W) at hsrc
    change Integrable (fun x => (Q x * u x) * φ x) (volume.restrict W) at hpot
    calc
      _ = ∫ x in W, ∑ i : Fin 3,
          p i x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
        simp only [matrixFlux, Matrix.one_apply, partialDeriv]
        simp
      _ = (∫ x in W, f x * φ x) / 8 + ∫ x in W, u x * (Q x * φ x) := heq φ hφ hc hs
      _ = ∫ x in W, (f x / 8 + Q x * u x) * φ x := by
        calc
          _ = (∫ x in W, f x * φ x) / 8 + ∫ x in W, (Q x * u x) * φ x := by
            congr 1
            apply integral_congr_ae
            exact Eventually.of_forall fun x => by ring
          _ = ∫ x in W, (f x * φ x) / 8 + (Q x * u x) * φ x := by
            rw [integral_add (hsrc.div_const _) hpot, integral_div]
          _ = _ := by
            apply integral_congr_ae
            exact Eventually.of_forall fun x => by ring
  have hf2' : MemWkpLocally 2 (fun x => f x / 8) W := by
    have h : MemWkpLocally 2 f W := hf2
    simpa only [div_eq_mul_inv, mul_comm] using h.smooth_mul (contDiff_const (c := (8 : ℝ)⁻¹))
  exact memWkpLocally_four_of_local_potential_H2_source
    (A := fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ))
    isClosed_singleton.isOpen_compl hW (isCompact_closure_cylinderAnnulus a b)
    (fun x hx => cylinderShell_ne_zero (closure_cylinderAnnulus_subset_shell a b hx))
    (fun _ _ => contDiff_const) (fun _ _ => Matrix.PosDef.one)
    (nativeHalfEndPotentialCoefficient_contDiffOn V hVs) hf2' hu
    (fun i => Lp.memLp (p i)) hpartial hweak

#print axioms native_forced_halfEnd_local_H4_on_annulus

end Yamabe3.Analysis.SpherePolar
