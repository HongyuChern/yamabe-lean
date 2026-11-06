import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndStrongLimit
import PoincareLib.Analysis.Elliptic.Regularity.Iteration.Bootstrap

/-!
# Local H2 of the same constructed forced half-end representative

The actual finite fields and their strong local H1 limit supply the weak
derivatives and the original physical weak equation. On each positive
annulus the physical source is L2 and the actual potential is bounded,
so the full principal source `f / 8 + Q * u` is L2. The pinned interior
difference-quotient theorem then gives local H2 of the same physical
function `cylinderLift w`.

The representatives are chosen once before all local domains. No H1 or
weak-PDE conclusion is assumed by the construction theorems below. The
conclusion is native weak Sobolev regularity only: a jointly measurable
representative is not asserted to be pointwise continuous or classical.
All domains remain inside the punctured unit ball.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal ContDiff Topology RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration

/-- Actual weak partials and an L2 principal source give local H2. The
split physical right-hand side is combined only after proving that both
pairings are integrable. -/
theorem native_memWkpLocally_two_of_split_weak_equation
    {O : Set E} (hO : IsOpen O) {u f Q : E → ℝ} {p : Fin 3 → E → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (hf : MemLp f 2 (volume.restrict O))
    (hQu : MemLp (fun x => Q x * u x) 2 (volume.restrict O))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i : Fin 3,
        p i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        (∫ x in O, f x * φ x) / 8 + ∫ x in O, u x * (Q x * φ x)) :
    MemWkpLocally 2 u O := by
  let g : E → ℝ := fun x => f x / 8 + Q x * u x
  have hg : MemLp g 2 (volume.restrict O) := by
    dsimp only [g]
    simp only [div_eq_mul_inv]
    change MemLp ((fun x => f x * (8 : ℝ)⁻¹) + (fun x => Q x * u x)) 2
      (volume.restrict O)
    exact (hf.mul_const ((8 : ℝ)⁻¹)).add hQu
  have hweak : WeakEquation O
      (matrixFlux (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ)) p) g := by
    intro φ hφ hc hs
    have hφL : MemLp φ 2 (volume.restrict O) :=
      (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
    have hsrc := hf.integrable_mul hφL
    have hpot := hQu.integrable_mul hφL
    change Integrable (fun x => f x * φ x) (volume.restrict O) at hsrc
    change Integrable (fun x => (Q x * u x) * φ x) (volume.restrict O) at hpot
    have hright : (∫ x in O, g x * φ x) =
        (∫ x in O, f x * φ x) / 8 + ∫ x in O, u x * (Q x * φ x) := by
      calc
        _ = ∫ x in O, (f x * φ x) / 8 + (Q x * u x) * φ x := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by dsimp only [g]; ring
        _ = (∫ x in O, f x * φ x) / 8 + ∫ x in O, (Q x * u x) * φ x := by
          rw [integral_add (hsrc.div_const _) hpot, integral_div]
        _ = _ := by
          congr 1
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by ring
    calc
      _ = ∫ x in O, ∑ i : Fin 3,
          p i x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
        simp only [matrixFlux, Matrix.one_apply, partialDeriv]
        simp
      _ = _ := (heq φ hφ hc hs).trans hright.symm
  exact memWkpLocally_add_two_of_weakEquation 0 hO
    (A := fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ))
    (fun _ _ => contDiff_const) (fun _ _ => Matrix.PosDef.one)
    hu hp hpartial (locally_of_memWkp hO (k := 0) hg) hweak

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The actual native Dirichlet construction has local H2 on each
positive annulus for the same fixed joint representative. The original
finite weak equations and the actual weak derivatives are produced by
the strong-limit theorem inside this proof. -/
theorem native_forced_halfEnd_local_H2_on_annulus
    {J : Type*} [Nonempty J] [SemilatticeSup J]
    [(atTop : Filter J).IsCountablyGenerated]
    (F : ℝ≥0 →ᵇ AngularL2) {s : J → Finset AngularIndex} (hs : Tendsto s atTop atTop)
    {w z : ℝ × S → ℝ} (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ))
    {a b : ℝ} (ha : 0 < a) :
    MemWkpLocally 2 (cylinderLift w) (cylinderAnnulus a b) := by
  obtain ⟨hH1, p, hpartial, -, -, heq⟩ :=
    native_forced_halfEnd_local_strong_equation hκ0 hκ1 V hV hV0 F hs
      hw hz hwAE hzAE (a := a / 2) (b := b + 1) (a' := a) (b' := b)
      (by linarith) (by linarith) (by linarith)
  let O := cylinderAnnulus a b
  let u := cylinderLift w
  let f := physicalForcing (fun q : ℝ × S => Real.exp (-2 * q.1) * z q)
  have hO : IsOpen O := isOpen_cylinderAnnulus a b
  have hu : MemLp u 2 (volume.restrict O) := hH1.1
  have hH : Continuous (fun t : ℝ => nativeHighProjection (F t.toNNReal)) :=
    nativeHighProjection.continuous.comp (F.continuous.comp continuous_real_toNNReal)
  have hf : MemLp f 2 (volume.restrict O) :=
    (memLp_halfEnd_physicalForcing_on_shell hH hz hzAE a b).mono_measure
      (Measure.restrict_mono (cylinderAnnulus_subset_shell a b) le_rfl)
  have hQu : MemLp (fun x => nativeHalfEndPotentialCoefficient V x * u x)
      2 (volume.restrict O) := by
    apply hu.of_le_mul (c := ‖V‖ / Real.exp (-b) ^ 2)
      ((nativeHalfEndPotentialCoefficient_measurable V).aestronglyMeasurable.mul
        hu.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    change ‖nativeHalfEndPotentialCoefficient V x * u x‖ ≤
      (‖V‖ / Real.exp (-b) ^ 2) * ‖u x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (nativeHalfEndPotentialCoefficient_norm_le_on_shell V
        (cylinderAnnulus_subset_shell a b hx)) (norm_nonneg (u x))
  exact native_memWkpLocally_two_of_split_weak_equation hO hu
    (fun i => Lp.memLp (p i)) hpartial hf hQu heq

/-- The same original measurable physical representative has native
local H2 throughout the punctured unit ball. No assertion is made at the
origin or across the entrance sphere. -/
theorem native_forced_halfEnd_local_H2
    {J : Type*} [Nonempty J] [SemilatticeSup J]
    [(atTop : Filter J).IsCountablyGenerated]
    (F : ℝ≥0 →ᵇ AngularL2) {s : J → Finset AngularIndex} (hs : Tendsto s atTop atTop)
    {w z : ℝ × S → ℝ} (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ)) :
    MemWkpLocally 2 (cylinderLift w) (Metric.ball (0 : E) 1 \ {(0 : E)}) := by
  intro x hx
  have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx.2
  have hxn : ‖x‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx.1
  let c := -Real.log ‖x‖
  have hc : 0 < c := neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr hx0) hxn)
  have ha : 0 < c / 2 := by linarith
  have hxA : x ∈ cylinderAnnulus (c / 2) (c + 1) :=
    mem_cylinderAnnulus_of_log_norm hx0
      (by change c / 2 < c; linarith) (by change c < c + 1; linarith)
  obtain ⟨W, hW, hxW, hWA, hWH2⟩ :=
    native_forced_halfEnd_local_H2_on_annulus hκ0 hκ1 V hV hV0 F hs
      hw hz hwAE hzAE (a := c / 2) (b := c + 1) ha x hxA
  have hAO : cylinderAnnulus (c / 2) (c + 1) ⊆
      Metric.ball (0 : E) 1 \ {(0 : E)} :=
    subset_closure.trans (closure_positive_cylinderAnnulus_subset_halfEnd ha)
  exact ⟨W, hW, hxW, hWA.trans hAO, hWH2⟩

/-- The actual construction supplies fixed joint representatives of the
same native solution and high source, and the original physical solution
has native local H2 on the whole punctured unit ball. -/
theorem exists_native_forced_halfEnd_local_H2 (F : ℝ≥0 →ᵇ AngularL2) :
    ∃ w z : ℝ × S → ℝ,
      Measurable w ∧ Measurable z ∧
      (∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ)) ∧
      (∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
        (nativeHighProjection (F t.toNNReal) : S → ℝ)) ∧
      MemWkpLocally 2 (cylinderLift w) (Metric.ball (0 : E) 1 \ {(0 : E)}) := by
  classical
  letI : Countable AngularIndex := countable_angularIndex_for_halfEnd
  obtain ⟨w, z, hw, hz, hwAE, hzAE, -⟩ :=
    exists_native_forced_halfEnd_local_strong_equation_finset hκ0 hκ1 V hV hV0 F
  refine ⟨w, z, hw, hz, hwAE, hzAE, ?_⟩
  exact native_forced_halfEnd_local_H2 (J := Finset AngularIndex)
    hκ0 hκ1 V hV hV0 F (s := id) tendsto_id hw hz hwAE hzAE

#print axioms native_memWkpLocally_two_of_split_weak_equation
#print axioms native_forced_halfEnd_local_H2_on_annulus
#print axioms native_forced_halfEnd_local_H2
#print axioms exists_native_forced_halfEnd_local_H2

end Yamabe3.Analysis.SpherePolar
