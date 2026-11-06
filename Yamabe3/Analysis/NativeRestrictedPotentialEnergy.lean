import Yamabe3.Analysis.NativeDomainEnergyInclusionCore
import Yamabe3.Analysis.PotentialForm

/-!
# The potential form restricted to the true native domain volume

Both L2 factors are restricted by the actual measure-restriction map.
The smooth multiplier is the existing native energy multiplier. Agreement
with the literal domain integral is proved on all smooth global tests;
density then identifies the form on a zero-boundary domain argument.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def restrictedPotentialH1NormedSpace (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] restrictedPotentialH1NormedSpace

/-- The genuine native potential pairing over the stated domain. -/
def nativeRestrictedPotentialForm (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V) :
    H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp
    ((LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω).comp
      ((toL2 g.leviCivitaData univ).comp
        (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) V hV)))
    ((LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω).comp (toL2 g.leviCivitaData univ))

@[simp] theorem nativeRestrictedPotentialForm_coe (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (f h : EnergyTest g.leviCivitaData univ) :
    nativeRestrictedPotentialForm g Ω V hV (f : H1Zero g.leviCivitaData univ)
      (h : H1Zero g.leviCivitaData univ) =
        ∫ x in Ω, V x * f x * h x ∂g.volumeMeasure := by
  change ⟪LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω
      (toL2 g.leviCivitaData univ (energyMulSmooth g.leviCivitaData univ
        (by simpa using isCompact_univ) V hV f)),
    LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω (toL2 g.leviCivitaData univ h)⟫_ℝ = _
  rw [energyMulSmooth_coe, toL2_coe, toL2_coe, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ Ω
      (testToL2 g.leviCivitaData univ (f.mulSmooth V hV)),
    LpToLpRestrictCLM_coeFn ℝ Ω (testToL2 g.leviCivitaData univ h),
    ae_restrict_of_ae (f.mulSmooth V hV).memLp.coeFn_toLp,
    ae_restrict_of_ae h.memLp.coeFn_toLp] with x hfR hhR hfV hh
  rw [hfR, hhR]
  change ⟪((f.mulSmooth V hV).memLp.toLp (f.mulSmooth V hV)) x,
    (h.memLp.toLp h) x⟫_ℝ = _
  rw [hfV, hh]
  simp [EnergyTest.mulSmooth_apply, mul_comm, mul_left_comm, mul_assoc]

theorem nativeRestrictedPotentialForm_symm (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (v w : H1Zero g.leviCivitaData univ) :
    nativeRestrictedPotentialForm g Ω V hV v w =
      nativeRestrictedPotentialForm g Ω V hV w v := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f =>
    induction w using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih h =>
      rw [nativeRestrictedPotentialForm_coe, nativeRestrictedPotentialForm_coe]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring

/-- The full zero-boundary domain space has no exterior potential term. -/
theorem nativeRestrictedPotentialForm_domain_right (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (v : H1Zero g.leviCivitaData univ) (z : H1Zero g.leviCivitaData Ω) :
    nativeRestrictedPotentialForm g Ω V hV v (nativeDomainEnergyInclusion g Ω z) =
      potentialForm g.leviCivitaData univ (by simpa using isCompact_univ) V hV v
        (nativeDomainEnergyInclusion g Ω z) := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f =>
    induction z using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih h =>
      rw [nativeDomainEnergyInclusion_coe, nativeRestrictedPotentialForm_coe, potentialForm_coe]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : h x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hh => hx (h.support_subset hh))
      change V x * f x * h x = 0
      rw [hz, mul_zero]

theorem nativeRestrictedPotentialForm_nonneg (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V) (hpos : ∀ x, 0 ≤ V x)
    (v : H1Zero g.leviCivitaData univ) : 0 ≤ nativeRestrictedPotentialForm g Ω V hV v v := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih f =>
    rw [nativeRestrictedPotentialForm_coe]
    apply integral_nonneg
    intro x
    change 0 ≤ V x * f x * f x
    simpa only [mul_assoc] using mul_nonneg (hpos x) (mul_self_nonneg (f x))

#print axioms nativeRestrictedPotentialForm_coe
#print axioms nativeRestrictedPotentialForm_domain_right

end Yamabe3.Analysis
