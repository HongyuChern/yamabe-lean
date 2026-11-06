import Yamabe3.Analysis.NativeBubbleHighPotential
import Yamabe3.Analysis.NativeDelaunayHalfEndPotential

/-!
Actual full-bubble and small-energy Delaunay instances of the high H1/L2
coupled inverse. The reflected exterior Poisson curve and the positive
half-line curve have actual one-sided derivatives at the same entrance.
This is a model-cylinder high-mode theorem. It neither produces a general
metric correction nor removes low-mode compensation.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace BoundedContinuousFunction ContDiff
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem fullBubbleDensity_even (t : ℝ) : fullBubbleDensity (-t) = fullBubbleDensity t := by
  unfold fullBubbleDensity
  rw [show 2 * -t = -(2*t) by ring, Real.exp_neg]
  field_simp
  <;> ring

/-- The cylinder coefficient is exactly r^2 times the physical linearized
potential of B(r)=sqrt(2/(1+r^2)), with Qp=15/4. -/
theorem fullBubbleDensity_physical (r : ℝ) (hr : 0 < r) :
    (15/4) * fullBubbleDensity (-Real.log r) =
      r^2 * (15/4) * (Real.sqrt (2/(1+r^2)))^4 := by
  rw [fullBubbleDensity_even]
  unfold fullBubbleDensity
  rw [show 2 * Real.log r = Real.log r + Real.log r by ring,
    Real.exp_add, Real.exp_log hr]
  have hs : Real.sqrt (2/(1+r^2))^2 = 2/(1+r^2) := Real.sq_sqrt (by positivity)
  rw [show Real.sqrt (2/(1+r^2))^4 = (Real.sqrt (2/(1+r^2))^2)^2 by ring, hs]
  field_simp
  <;> ring

theorem fullBubble_exterior_potential (t₀ s : ℝ) :
    (fullBubbleHighPotential (-t₀)).potential s = (15/4) * fullBubbleDensity (t₀-s) := by
  change (15/4) * fullBubbleDensity (s + -t₀) = _
  rw [show s + -t₀ = -(t₀-s) by ring, fullBubbleDensity_even]

namespace NativeHighPotential

def curve (P : NativeHighPotential) (b : AngularH1) : ℝ → AngularL2 :=
  nativeHalfHighPotentialPhysical P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg b

def curveDerivative (P : NativeHighPotential) (b : AngularH1) : ℝ → AngularL2 :=
  nativeHalfHighPotentialPhysicalDerivative P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg b

theorem curve_zero (P : NativeHighPotential) (b : AngularH1)
    (hb : nativeHighEnergyProjectionCLM b = b) : P.curve b 0 = angularEmbedding b := by
  rw [curve, nativeHalfHighPotentialPhysical_zero, hb]

theorem curve_right_derivative (P : NativeHighPotential) (b : AngularH1) :
    HasDerivWithinAt (P.curve b) (-P.dtn b) (Ici 0) 0 := by
  have h := nativeHalfHighPotentialPhysical_hasDerivWithinAt
    P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg b 0 le_rfl
  simpa only [dtn, nativeHighDtN_apply, neg_neg, curve] using h

theorem reflected_curve_left_derivative (P : NativeHighPotential) (b : AngularH1) :
    HasDerivWithinAt (fun t : ℝ => P.curve b (-t)) (P.dtn b) (Iic 0) 0 := by
  have h := (P.curve_right_derivative b).scomp_of_eq 0
    (hasDerivAt_id (0:ℝ)).neg.hasDerivWithinAt
    (show MapsTo (fun t : ℝ => -t) (Iic 0) (Ici 0) from fun t ht => mem_Ici.mpr (neg_nonneg.mpr (mem_Iic.mp ht)))
    (by simp)
  simpa only [Function.comp_def, Pi.neg_apply, id_eq, neg_smul, one_smul, neg_neg] using h

end NativeHighPotential

/-- One sigma simultaneously gives the literal value jump and the
signed derivative jump of the two actual Poisson fields. -/
theorem exists_actual_high_poisson_cauchy_matching (B W : NativeHighPotential)
    (d : AngularH1) (hd : nativeHighEnergyProjectionCLM d = d)
    (n : AngularL2) (hn : nativeHighProjection n = n) :
    ∃ σ : AngularH1, nativeHighEnergyProjectionCLM σ = σ ∧
      (B.curve (σ+d) 0 - W.curve σ 0 = angularEmbedding d) ∧
      HasDerivWithinAt (fun t : ℝ => B.curve (σ+d) (-t)) (B.dtn (σ+d)) (Iic 0) 0 ∧
      HasDerivWithinAt (W.curve σ) (-W.dtn σ) (Ici 0) 0 ∧
      B.dtn (σ+d) - (-W.dtn σ) = n := by
  obtain ⟨σ, hs, hsd, _, he⟩ := exists_nativeHighCoupled_cauchy_matching B W d hd n hn
  refine ⟨σ, hs, ?_, B.reflected_curve_left_derivative _, W.curve_right_derivative _, ?_⟩
  · rw [B.curve_zero _ hsd, W.curve_zero _ hs, map_add]
    abel
  · simpa only [sub_neg_eq_add] using he

/-- The exact paper correction equation, with both bubble orientations
and the same high trace. This does not assert that eta is a Green kernel. -/
theorem fullBubble_high_tail_correction (t₀ : ℝ) (W : NativeHighPotential)
    (η : AngularH1) (hη : nativeHighEnergyProjectionCLM η = η) :
    let Bm := fullBubbleHighPotential (-t₀)
    let Bp := fullBubbleHighPotential t₀
    let δ := -nativeHighCoupledDtNInverse Bm W ((W.dtn - Bp.dtn) η)
    nativeHighEnergyProjectionCLM δ = δ ∧
      -Bp.dtn η + Bm.dtn δ = -W.dtn (η+δ) := by
  dsimp only
  let Bm := fullBubbleHighPotential (-t₀)
  let Bp := fullBubbleHighPotential t₀
  let f := (W.dtn - Bp.dtn) η
  have hf : nativeHighProjection f = f := by
    change nativeHighProjection (W.dtn η - Bp.dtn η) = _
    rw [map_sub, W.high, Bp.high]
    rfl
  have he : (Bm.dtn + W.dtn) (-nativeHighCoupledDtNInverse Bm W f) = -f := by
    rw [map_neg, nativeHighCoupledDtNInverse_right, hf]
  refine ⟨by rw [map_neg, nativeHighCoupledDtNInverse_high], ?_⟩
  change Bm.dtn (-nativeHighCoupledDtNInverse Bm W f) +
    W.dtn (-nativeHighCoupledDtNInverse Bm W f) = -(W.dtn η - Bp.dtn η) at he
  rw [map_add]
  have he' := eq_sub_of_add_eq he
  dsimp only [f, Bm, Bp] at he'
  rw [he']
  abel

/-- The original same-orbit producer supplies all potential conditions
uniformly before the orbit and phase. The resulting inverse is then
constructed, never passed as an argument. -/
theorem exists_uniform_bubble_delaunay_coupled_inverse :
    ∃ q₀ : ℝ, 0 < q₀ ∧ ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
      (∀ t, deriv (deriv v) t = radialForce (v t)) → 0 < v 0 →
      ∀ q : ℝ, 0 < q → q < q₀ → q = v 0^2 - v 0^6 - 4 * deriv v 0^2 →
      ∀ τ : ℝ, ∃ W : NativeHighPotential,
        (∀ t, W.potential t = (15/4) * v (t+τ)^4) ∧
        ∀ t₀ : ℝ, ∃ R : AngularL2 →L[ℝ] AngularH1,
          (∀ f, (fullBubbleHighPotential (-t₀)).dtn (R f) + W.dtn (R f) = nativeHighProjection f) ∧
          (∀ b, R ((fullBubbleHighPotential (-t₀)).dtn b + W.dtn b) = nativeHighEnergyProjectionCLM b) ∧
          (∀ f, ‖R f‖ ≤ 2 * ‖f‖) := by
  obtain ⟨κ, q₀, hκ0, hκ1, hq₀, hp⟩ := exists_uniform_small_energy_halfEnd_phase_potential
  refine ⟨q₀, hq₀, ?_⟩
  intro v hv ho hv0 q hq hqq hE τ
  obtain ⟨hb, hall⟩ := hp v hv ho hv0 q hq hqq hE
  let W : NativeHighPotential := {
    κ := κ, κ_nonneg := hκ0, κ_lt_one := hκ1
    potential := delaunayPhasePotentialBCF v hv.continuous hb τ
    kernel_bound := (hall τ).2.2.2
    nonneg := (hall τ).1
    upper := fun t _ => (hall τ).2.1 t }
  refine ⟨W, fun _ => rfl, ?_⟩
  intro t₀
  refine ⟨nativeHighCoupledDtNInverse (fullBubbleHighPotential (-t₀)) W, ?_, ?_, ?_⟩
  · exact nativeHighCoupledDtNInverse_right _ W
  · exact nativeHighCoupledDtNInverse_left _ W
  · exact nativeHighCoupledDtNInverse_norm _ W

#print axioms fullBubbleDensity_physical
#print axioms exists_actual_high_poisson_cauchy_matching
#print axioms fullBubble_high_tail_correction
#print axioms exists_uniform_bubble_delaunay_coupled_inverse
end Yamabe3.Analysis.Delaunay
