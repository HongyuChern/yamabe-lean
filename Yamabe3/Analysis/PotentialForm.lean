import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.WeakDirichlet
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Weighted.Multiplication

/-!
# The actual bounded-potential form on the retained H1 completion

The potential term is constructed using the upstream smooth multiplier and
L2 embedding. Its agreement with the integral on smooth compact tests is
proved below. No inverse, coercivity estimate, or Poincare inequality is an
input structure. In particular, the pure-gradient Dirichlet Poincare theorem
is not applied to the whole of a closed manifold.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
/-- Compactness supplies the genuine finite potential lower bound; it
does not have to be added to a closed-manifold target as a new hypothesis. -/
theorem exists_nonneg_potential_lower_bound [CompactSpace M]
    (V : M → ℝ) (hV : Continuous V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, -B ≤ V x := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hV.continuousOn
  refine ⟨max C 0, le_max_right C 0, fun x => ?_⟩
  have habs : |V x| ≤ max C 0 := by
    have hx : |V x| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC x (mem_univ x)
    exact hx.trans (le_max_left C 0)
  exact (neg_le_neg habs).trans (neg_abs_le (V x))

/-- The potential contribution as an actual continuous bilinear form on
the upstream Dirichlet H1 completion. -/
def potentialForm (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V) :
    H1Zero D Ω →L[ℝ] H1Zero D Ω →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp
    ((toL2 D Ω).comp (energyMulSmooth D Ω hc V hV)) (toL2 D Ω)

@[simp] theorem potentialForm_apply (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V) (v w : H1Zero D Ω) :
    potentialForm D Ω hc V hV v w =
      ⟪toL2 D Ω (energyMulSmooth D Ω hc V hV v), toL2 D Ω w⟫_ℝ := rfl

/-- The continuous form is exactly the retained-volume potential integral
on genuine smooth tests. -/
@[simp] theorem potentialForm_coe (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V) (f h : EnergyTest D Ω) :
    potentialForm D Ω hc V hV (f : H1Zero D Ω) (h : H1Zero D Ω) =
      ∫ x, V x * f x * h x ∂g.volumeMeasure := by
  simp only [potentialForm_apply, energyMulSmooth_coe, toL2_coe,
    testToL2_inner, EnergyTest.mulSmooth_apply]

theorem potentialForm_symm (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V) (v w : H1Zero D Ω) :
    potentialForm D Ω hc V hV v w = potentialForm D Ω hc V hV w v := by
  induction v using Completion.induction_on with
  | hp =>
    apply isClosed_eq <;> fun_prop
  | ih f =>
    induction w using Completion.induction_on with
    | hp =>
      apply isClosed_eq <;> fun_prop
    | ih h =>
      rw [potentialForm_coe, potentialForm_coe]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring

/-- A genuine pointwise lower bound on the potential extends by density
to the completed form. It is measured by the L2 norm, not the H1 norm. -/
theorem potentialForm_self_lower (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V) (B : ℝ)
    (hB : ∀ x, -B ≤ V x) (v : H1Zero D Ω) :
    -B * ‖toL2 D Ω v‖ ^ 2 ≤ potentialForm D Ω hc V hV v v := by
  induction v using Completion.induction_on with
  | hp =>
    apply isClosed_le <;> fun_prop
  | ih f =>
    rw [potentialForm_coe, toL2_coe]
    calc
      -B * ‖testToL2 D Ω f‖ ^ 2 =
          ∫ x, -B * (f x * f x) ∂g.volumeMeasure := by
        rw [integral_const_mul, ← testToL2_inner, real_inner_self_eq_norm_sq]
      _ ≤ ∫ x, V x * f x * f x ∂g.volumeMeasure := by
        apply integral_mono ((f.integrable_mul f).const_mul (-B))
          ((f.mulSmooth V hV).integrable_mul f)
        intro x
        simpa only [EnergyTest.mulSmooth_apply, mul_assoc] using
          mul_le_mul_of_nonneg_right (hB x) (mul_self_nonneg (f x))

/-- The actual weak energy form for `-a Δ + V`. -/
def schrodingerForm (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (a : ℝ) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V) :
    H1Zero D Ω →L[ℝ] H1Zero D Ω →L[ℝ] ℝ :=
  a • gradientEnergy D Ω + potentialForm D Ω hc V hV

theorem schrodingerForm_apply (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (a : ℝ) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V) (v w : H1Zero D Ω) :
    schrodingerForm D Ω hc a V hV v w =
      a * gradientEnergy D Ω v w + potentialForm D Ω hc V hV v w := rfl

theorem schrodingerForm_coe (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (a : ℝ) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V) (f h : EnergyTest D Ω) :
    schrodingerForm D Ω hc a V hV (f : H1Zero D Ω) (h : H1Zero D Ω) =
      ∫ x, (a * g.inner x (D.gradient f x) (D.gradient h x) +
        V x * f x * h x) ∂g.volumeMeasure := by
  have hpot : Integrable (fun x => V x * f x * h x) g.volumeMeasure := by
    simpa only [EnergyTest.mulSmooth_apply] using ((f.mulSmooth V hV).integrable_mul h)
  rw [schrodingerForm_apply, gradientEnergy_coe, potentialForm_coe,
    integral_add ((f.integrable_gradient h).const_mul a)
      hpot, integral_const_mul]

theorem schrodingerForm_symm (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (a : ℝ) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V) (v w : H1Zero D Ω) :
    schrodingerForm D Ω hc a V hV v w =
      schrodingerForm D Ω hc a V hV w v := by
  rw [schrodingerForm_apply, schrodingerForm_apply,
    gradientEnergy_symm, potentialForm_symm]

/-- Density transports an explicitly stated smooth-test L2 inequality to
the completed space. The inequality on tests is a proof obligation, not an
assumption of the final Yamabe target. -/
theorem schrodingerForm_L2_lower_of_tests (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (a κ : ℝ) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (hgap : ∀ f : EnergyTest D Ω, κ * ‖testToL2 D Ω f‖ ^ 2 ≤
      schrodingerForm D Ω hc a V hV (f : H1Zero D Ω) (f : H1Zero D Ω))
    (v : H1Zero D Ω) :
    κ * ‖toL2 D Ω v‖ ^ 2 ≤ schrodingerForm D Ω hc a V hV v v := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih f => simpa only [toL2_coe] using hgap f

/-- A proven smooth-test L2 gap, together with an actual potential lower
bound, implies full H1 coercivity. This theorem does not assert that a
positive Yamabe constant has already supplied its `hgap` hypothesis. -/
theorem schrodingerForm_isCoercive_of_testL2_lower
    (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (a κ B : ℝ) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (ha : 0 < a) (hκ : 0 < κ) (hB : 0 ≤ B) (hVB : ∀ x, -B ≤ V x)
    (hgap : ∀ f : EnergyTest D Ω, κ * ‖testToL2 D Ω f‖ ^ 2 ≤
      schrodingerForm D Ω hc a V hV (f : H1Zero D Ω) (f : H1Zero D Ω)) :
    IsCoercive (schrodingerForm D Ω hc a V hV) := by
  have hden : 0 < κ + B + a := by positivity
  refine ⟨a * κ / (κ + B + a), by positivity, fun v => ?_⟩
  have hnorm : ‖v‖ ^ 2 = gradientEnergy D Ω v v + ‖toL2 D Ω v‖ ^ 2 := by
    rw [gradientEnergy_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hlower : a * gradientEnergy D Ω v v - B * ‖toL2 D Ω v‖ ^ 2 ≤
      schrodingerForm D Ω hc a V hV v v := by
    rw [schrodingerForm_apply]
    linarith [potentialForm_self_lower D Ω hc V hV B hVB v]
  have hfull := schrodingerForm_L2_lower_of_tests D Ω hc a κ V hV hgap v
  have hone := mul_le_mul_of_nonneg_left hlower (le_of_lt hκ)
  have htwo := mul_le_mul_of_nonneg_left hfull (show 0 ≤ B + a by positivity)
  have hcombined : a * κ * ‖v‖ ^ 2 ≤
      (κ + B + a) * schrodingerForm D Ω hc a V hV v v := by
    rw [hnorm]
    nlinarith
  calc
    (a * κ / (κ + B + a)) * ‖v‖ * ‖v‖ =
        (a * κ * ‖v‖ ^ 2) / (κ + B + a) := by ring
    _ ≤ schrodingerForm D Ω hc a V hV v v :=
      (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hcombined)

#print axioms potentialForm_coe
#print axioms exists_nonneg_potential_lower_bound
#print axioms potentialForm_self_lower
#print axioms schrodingerForm_coe
#print axioms schrodingerForm_isCoercive_of_testL2_lower

end Yamabe3.Analysis
