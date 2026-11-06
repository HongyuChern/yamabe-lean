import Yamabe3.Analysis.NativeTraceZeroExteriorRestriction
import Yamabe3.Analysis.NativeRestrictedPotentialLocality
import Yamabe3.Analysis.NativePhysicalTraceQuotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Weak conormal on the actual physical sphere trace quotient

The data are an element of the original native H1 completion and an
actual L2 source for the original Riemannian volume. Their admissibility
is the genuine variational equation against the actual exterior H1-zero
space. No annihilation of a trace kernel is an input.

The proved one-sided restriction of a zero-trace test supplies both its
actual indicator L2 value and its independent gradient locality identity.
These facts imply that energy minus source annihilates the actual trace
kernel. Composition with the actual minimum-energy quotient lifting then
defines a continuous conormal in the dual of the genuine trace space.

This dual is the intrinsic H^(-1/2)-type space associated with the proved
H1 trace quotient and its quotient energy norm. No identification with a
separately defined fractional Sobolev space is asserted. No pointwise
normal derivative is assumed for a weak solution.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option quotPrecheck false

open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff InnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT.LeviCivitaData.Dirichlet SpherePolar

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def weakPhysicalConormalH1NormedSpace (g : RiemannianMetric 3 M) (Ω : Set M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData Ω) := inferInstance
attribute [local instance] weakPhysicalConormalH1NormedSpace

/-- Restriction of the same native L2 value loses no more than its
original H1 norm; the constant is exactly one. -/
theorem nativeRestrictedL2CLM_apply_norm_le
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (v : H1Zero g.leviCivitaData univ) :
    ‖nativeRestrictedL2CLM g Ω v‖ ≤ ‖v‖ :=
  (norm_Lp_toLp_restrict_le Ω (toL2 g.leviCivitaData univ v)).trans (norm_toL2_le v)

/-- The actual source integral, linear and continuous in both the
original volume L2 source and the original completed test. -/
def nativeRestrictedL2SourceOperator (g : RiemannianMetric 3 M) (Ω : Set M) :
    Lp ℝ 2 g.volumeMeasure →L[ℝ] H1Zero g.leviCivitaData univ →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω)
    (nativeRestrictedL2CLM g Ω)

theorem nativeRestrictedL2SourceOperator_integrable
    (g : RiemannianMetric 3 M) (Ω : Set M) (F : Lp ℝ 2 g.volumeMeasure)
    (v : H1Zero g.leviCivitaData univ) :
    IntegrableOn (fun x => F x * toL2 g.leviCivitaData univ v x) Ω g.volumeMeasure :=
  ((Lp.memLp F).integrable_mul (Lp.memLp (toL2 g.leviCivitaData univ v))).integrableOn

theorem nativeRestrictedL2SourceOperator_apply
    (g : RiemannianMetric 3 M) (Ω : Set M) (F : Lp ℝ 2 g.volumeMeasure)
    (v : H1Zero g.leviCivitaData univ) :
    nativeRestrictedL2SourceOperator g Ω F v =
      ∫ x in Ω, F x * toL2 g.leviCivitaData univ v x ∂g.volumeMeasure := by
  change inner ℝ (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω F)
    (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω (toL2 g.leviCivitaData univ v)) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ Ω F,
    LpToLpRestrictCLM_coeFn ℝ Ω (toL2 g.leviCivitaData univ v)] with x hF hv
  rw [hF, hv]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem nativeRestrictedL2SourceOperator_apply_norm_le
    (g : RiemannianMetric 3 M) (Ω : Set M) (F : Lp ℝ 2 g.volumeMeasure)
    (v : H1Zero g.leviCivitaData univ) :
    ‖nativeRestrictedL2SourceOperator g Ω F v‖ ≤
      ‖LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω F‖ * ‖v‖ := by
  change ‖inner ℝ (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω F)
    (nativeRestrictedL2CLM g Ω v)‖ ≤ _
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (nativeRestrictedL2CLM_apply_norm_le g Ω v) (norm_nonneg _))

theorem nativeRestrictedL2SourceOperator_norm_le
    (g : RiemannianMetric 3 M) (Ω : Set M) (F : Lp ℝ 2 g.volumeMeasure) :
    ‖nativeRestrictedL2SourceOperator g Ω F‖ ≤
      ‖LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact nativeRestrictedL2SourceOperator_apply_norm_le g Ω F

theorem nativeRestrictedL2SourceOperator_eq_of_exterior_value
    (g : RiemannianMetric 3 M) (Ω : Set M) (hΩ : MeasurableSet Ω)
    (F : Lp ℝ 2 g.volumeMeasure) (v w : H1Zero g.leviCivitaData univ)
    (hvalue : (toL2 g.leviCivitaData univ w : M → ℝ) =ᵐ[g.volumeMeasure]
      Ω.indicator (toL2 g.leviCivitaData univ v)) :
    nativeRestrictedL2SourceOperator g Ω F v = nativeRestrictedL2SourceOperator g Ω F w := by
  rw [nativeRestrictedL2SourceOperator_apply, nativeRestrictedL2SourceOperator_apply]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hvalue, self_mem_ae_restrict hΩ] with x hx hmem
  rw [indicator_of_mem hmem] at hx
  rw [hx]

/-- The actual completed potential pairing is the literal native volume
integral of the same representatives; no weak boundary restriction occurs. -/
theorem nativeRestrictedPotentialForm_integral
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (u v : H1Zero g.leviCivitaData univ) :
    nativeRestrictedPotentialForm g Ω V hV u v =
      ∫ x in Ω, V x * toL2 g.leviCivitaData univ u x *
        toL2 g.leviCivitaData univ v x ∂g.volumeMeasure := by
  let m := energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) V hV u
  change inner ℝ (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω
    (toL2 g.leviCivitaData univ m))
    (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω (toL2 g.leviCivitaData univ v)) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ Ω (toL2 g.leviCivitaData univ m),
    LpToLpRestrictCLM_coeFn ℝ Ω (toL2 g.leviCivitaData univ v),
    ae_restrict_of_ae (native_energyMulSmooth_toL2_ae g V hV u)] with x hm hv hmul
  rw [hm, hv, hmul]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem nativeRestrictedPotentialForm_integrable
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (u v : H1Zero g.leviCivitaData univ) :
    IntegrableOn (fun x => V x * toL2 g.leviCivitaData univ u x *
      toL2 g.leviCivitaData univ v x) Ω g.volumeMeasure := by
  have hmul : MemLp (fun x => V x * toL2 g.leviCivitaData univ u x) 2 g.volumeMeasure :=
    MemLp.ae_eq (native_energyMulSmooth_toL2_ae g V hV u)
      (Lp.memLp (toL2 g.leviCivitaData univ
        (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) V hV u)))
  exact (hmul.integrable_mul (Lp.memLp (toL2 g.leviCivitaData univ v))).integrableOn

/-- The actual domain energy for -8 Delta_g + V. -/
def nativeRestrictedEllipticForm (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V) :
    H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ →L[ℝ] ℝ :=
  (8 : ℝ) • nativeRestrictedGradientEnergy g Ω + nativeRestrictedPotentialForm g Ω V hV

theorem nativeRestrictedEllipticForm_apply
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (u v : H1Zero g.leviCivitaData univ) :
    nativeRestrictedEllipticForm g Ω V hV u v =
      8 * nativeRestrictedGradientEnergy g Ω u v + nativeRestrictedPotentialForm g Ω V hV u v := rfl

theorem nativeRestrictedEllipticForm_norm_le
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V) :
    ‖nativeRestrictedEllipticForm g Ω V hV‖ ≤ 8 + ‖nativeRestrictedPotentialForm g Ω V hV‖ := by
  letI : NormSMulClass ℝ (H1Zero g.leviCivitaData univ →L[ℝ]
    H1Zero g.leviCivitaData univ →L[ℝ] ℝ) := by
      exact NormedSpace.toNormSMulClass (𝕜 := ℝ)
        (E := H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ →L[ℝ] ℝ)
  calc
    _ ≤ ‖(8 : ℝ) • nativeRestrictedGradientEnergy g Ω‖ +
        ‖nativeRestrictedPotentialForm g Ω V hV‖ := by
      exact ContinuousLinearMap.opNorm_add_le
        ((8 : ℝ) • nativeRestrictedGradientEnergy g Ω) (nativeRestrictedPotentialForm g Ω V hV)
    _ = 8 * ‖nativeRestrictedGradientEnergy g Ω‖ +
        ‖nativeRestrictedPotentialForm g Ω V hV‖ := by rw [norm_smul]; norm_num
    _ ≤ _ := by
      have h := nativeRestrictedGradientEnergy_norm_le g Ω
      nlinarith only [h]

/-- Energy minus the same actual source, on the genuine data product. -/
def nativeWeakEnergySourceDataCLM (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V) :
    (H1Zero g.leviCivitaData univ × Lp ℝ 2 g.volumeMeasure) →L[ℝ]
      H1Zero g.leviCivitaData univ →L[ℝ] ℝ :=
  (nativeRestrictedEllipticForm g Ω V hV).comp (ContinuousLinearMap.fst ℝ _ _) -
    (nativeRestrictedL2SourceOperator g Ω).comp (ContinuousLinearMap.snd ℝ _ _)

theorem nativeWeakEnergySourceDataCLM_apply
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (d : H1Zero g.leviCivitaData univ × Lp ℝ 2 g.volumeMeasure)
    (v : H1Zero g.leviCivitaData univ) :
    nativeWeakEnergySourceDataCLM g Ω V hV d v =
      nativeRestrictedEllipticForm g Ω V hV d.1 v - nativeRestrictedL2SourceOperator g Ω d.2 v := rfl

theorem nativeWeakEnergySourceDataCLM_apply_norm_le
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (d : H1Zero g.leviCivitaData univ × Lp ℝ 2 g.volumeMeasure) :
    ‖nativeWeakEnergySourceDataCLM g Ω V hV d‖ ≤
      (8 + ‖nativeRestrictedPotentialForm g Ω V hV‖) * ‖d.1‖ +
        ‖LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω d.2‖ := by
  change ‖nativeRestrictedEllipticForm g Ω V hV d.1 - nativeRestrictedL2SourceOperator g Ω d.2‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add
    (((nativeRestrictedEllipticForm g Ω V hV).le_opNorm d.1).trans
      (mul_le_mul_of_nonneg_right (nativeRestrictedEllipticForm_norm_le g Ω V hV) (norm_nonneg _)))
    (nativeRestrictedL2SourceOperator_norm_le g Ω d.2))

/-- The real weak equation, on the actual H1-zero test space. The
carrier condition refers to the domain inclusion, never to a trace kernel. -/
def NativeWeakEllipticDataSpace (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V) :
    Submodule ℝ (H1Zero g.leviCivitaData univ × Lp ℝ 2 g.volumeMeasure) where
  carrier := {d | ∀ z : H1Zero g.leviCivitaData Ω,
    nativeWeakEnergySourceDataCLM g Ω V hV d (nativeDomainEnergyInclusion g Ω z) = 0}
  zero_mem' := by intro z; rw [map_zero, ContinuousLinearMap.zero_apply]
  add_mem' := by
    intro d₁ d₂ hd₁ hd₂ z
    rw [map_add, ContinuousLinearMap.add_apply, hd₁ z, hd₂ z, add_zero]
  smul_mem' := by
    intro c d hd z
    rw [map_smul, ContinuousLinearMap.smul_apply, hd z, smul_zero]

/-- Membership is precisely the native variational equation with the
literal original-volume source integral. -/
theorem mem_NativeWeakEllipticDataSpace_iff
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (d : H1Zero g.leviCivitaData univ × Lp ℝ 2 g.volumeMeasure) :
    d ∈ NativeWeakEllipticDataSpace g Ω V hV ↔
      ∀ z : H1Zero g.leviCivitaData Ω,
        8 * gradientEnergy g.leviCivitaData univ d.1 (nativeDomainEnergyInclusion g Ω z) +
          potentialForm g.leviCivitaData univ (by simpa using isCompact_univ) V hV d.1
            (nativeDomainEnergyInclusion g Ω z) =
          ∫ x in Ω, d.2 x * toL2 g.leviCivitaData Ω z x ∂g.volumeMeasure := by
  change (∀ z : H1Zero g.leviCivitaData Ω,
    nativeWeakEnergySourceDataCLM g Ω V hV d (nativeDomainEnergyInclusion g Ω z) = 0) ↔ _
  simp only [nativeWeakEnergySourceDataCLM_apply, nativeRestrictedEllipticForm_apply,
    nativeRestrictedGradientEnergy_domain_right, nativeRestrictedPotentialForm_domain_right,
    nativeRestrictedL2SourceOperator_apply, nativeDomainEnergyInclusion_toL2, sub_eq_zero]

instance nativeWeakEllipticDataSpace_closed
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V) :
    IsClosed (NativeWeakEllipticDataSpace g Ω V hV : Set
      (H1Zero g.leviCivitaData univ × Lp ℝ 2 g.volumeMeasure)) := by
  change IsClosed {d | ∀ z : H1Zero g.leviCivitaData Ω,
    nativeWeakEnergySourceDataCLM g Ω V hV d (nativeDomainEnergyInclusion g Ω z) = 0}
  simp only [setOf_forall]
  exact isClosed_iInter fun z => isClosed_eq (by fun_prop) continuous_const

theorem nativeWeakEllipticDataSpace_complete
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V) :
    CompleteSpace (NativeWeakEllipticDataSpace g Ω V hV) := inferInstance

namespace EuclideanSphereTrace

open NativeChartSphereMetric

private theorem weakConormal_annulus_subset_source
    (e : OpenPartialHomeomorph E M) {a : ℝ}
    (hs : closedBall (0 : E) (2 * a) ⊆ e.source) :
    sphereTraceAnnulus a (2 * a) ⊆ e.source := by
  intro x hx
  exact hs (by simpa only [mem_closedBall, dist_zero_right] using hx.2)

private theorem weakConormal_annulus_coefficients
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M) {a : ℝ}
    (hcoeff : ∀ x ∈ closedBall (0 : E) (2 * a),
      gE.euclideanCoefficients x = g.pullbackCoefficients e x) :
    ∀ x ∈ sphereTraceAnnulus a (2 * a),
      gE.euclideanCoefficients x = g.pullbackCoefficients e x := by
  intro x hx
  exact hcoeff x (by simpa only [mem_closedBall, dist_zero_right] using hx.2)

section Exterior

variable (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
  (e : OpenPartialHomeomorph E M)
  (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
  {a C : ℝ} (ha : 0 < a)
  (hs : closedBall (0 : E) (2 * a) ⊆ e.source)
  (hcoeff : ∀ x ∈ closedBall (0 : E) (2 * a),
    gE.euclideanCoefficients x = g.pullbackCoefficients e x)
  (hC : 0 ≤ C)
  (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (a • (θ : E)) ≤ C)

local notation "hAnn" => weakConormal_annulus_subset_source e hs
local notation "hCoeffAnn" => weakConormal_annulus_coefficients g gE e hcoeff
local notation "hrInner" => (show a ∈ Icc a (2 * a) from ⟨le_rfl, by linarith only [ha]⟩)
local notation "habInner" => (show a < 2 * a from by linarith only [ha])
local notation "hθInner" => (fun θ : S => radial_mem_sphereTraceAnnulus ha hrInner θ)
local notation "T" => nativePhysicalSphereTraceCLM g gE e he hei ha habInner hrInner hAnn hC
  (fun θ => hCoeffAnn _ (hθInner θ)) (fun θ => hGauss (a • (θ : E))) hρ
local notation "Ω" => (e '' closedBall (0 : E) a)ᶜ
local notation "H" => H1Zero g.leviCivitaData univ
local notation "Q" => HilbertTraceQuotient.Space T
local notation "qmap" => HilbertTraceQuotient.quotientMap T
local notation "lift" => HilbertTraceQuotient.minimumLift T

/-- The dual of the actual physical trace quotient, equipped with its
operator norm. This is the intrinsic negative-half boundary data type. -/
abbrev NativePhysicalSphereWeakConormalSpace := Q →L[ℝ] ℝ

variable (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)

local notation "Data" => NativeWeakEllipticDataSpace g Ω V hV
local notation "ell" => nativeWeakEnergySourceDataCLM g Ω V hV

/-- Kernel annihilation is a conclusion of the actual variational PDE,
the actual one-sided zero-trace restriction and its proved gradient
locality. No geometric normal derivative is part of the input. -/
theorem nativeWeakEnergySource_annihilates_physical_trace_kernel
    (d : Data) (v : H) (hv : T v = 0) : ell d.val v = 0 := by
  have hΩ : MeasurableSet Ω :=
    ((isCompact_closedBall (0 : E) a).image_of_continuousOn
      (e.continuousOn.mono ((closedBall_subset_closedBall (by linarith only [ha])).trans hs))).measurableSet.compl
  obtain ⟨z, hz, _, hgrad⟩ := exists_native_zero_trace_exterior_restriction
    g gE e he hei hGauss ha hs hcoeff hC hρ v hv
  have hvalue : (toL2 g.leviCivitaData univ (nativeDomainEnergyInclusion g Ω z) : M → ℝ)
      =ᵐ[g.volumeMeasure] (Ω).indicator (toL2 g.leviCivitaData univ v) := by
    simpa only [nativeDomainEnergyInclusion_toL2] using hz
  have hpot := nativeRestrictedPotentialForm_eq_of_exterior_value
    g Ω hΩ V hV d.val.1 v (nativeDomainEnergyInclusion g Ω z) hvalue
  have hsrc := nativeRestrictedL2SourceOperator_eq_of_exterior_value
    g Ω hΩ d.val.2 v (nativeDomainEnergyInclusion g Ω z) hvalue
  have heq : ell d.val v = ell d.val (nativeDomainEnergyInclusion g Ω z) := by
    rw [nativeWeakEnergySourceDataCLM_apply, nativeWeakEnergySourceDataCLM_apply,
      nativeRestrictedEllipticForm_apply, nativeRestrictedEllipticForm_apply,
      hgrad d.val.1, nativeRestrictedGradientEnergy_domain_right, hpot, hsrc]
  rw [heq]
  exact d.property z

/-- The weak conormal is linear and continuous in the genuine solution
and source data. The map uses the actual minimum-energy trace lifting. -/
def nativeWeakPhysicalConormalCLM : Data →L[ℝ] NativePhysicalSphereWeakConormalSpace
    g gE e he hei hGauss ha hs hcoeff hC hρ :=
  ((ContinuousLinearMap.compL ℝ Q H ℝ).flip (lift).toContinuousLinearMap).comp
    ((ell).comp (Data).subtypeL)

theorem nativeWeakPhysicalConormalCLM_apply (d : Data) (q : Q) :
    nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d q =
      ell d.val (lift q) := rfl

/-- Every global H1 lifting, including a nonzero boundary test, gives
the same functional. The kernel statement used here was proved above. -/
theorem nativeWeakPhysicalConormal_quotientMap (d : Data) (v : H) :
    nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d (qmap v) =
      ell d.val v := by
  have hzero : T (v - lift (qmap v)) = 0 := by
    rw [map_sub, HilbertTraceQuotient.trace_minimumLift,
      HilbertTraceQuotient.value_quotientMap, sub_self]
  have h := nativeWeakEnergySource_annihilates_physical_trace_kernel
    g gE e he hei hGauss ha hs hcoeff hC hρ V hV d (v - lift (qmap v)) hzero
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem nativeWeakPhysicalConormal_factorization (d : Data) :
    (nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d).comp qmap =
      ell d.val := by
  apply ContinuousLinearMap.ext
  exact nativeWeakPhysicalConormal_quotientMap g gE e he hei hGauss ha hs hcoeff hC hρ V hV d

/-- The value is independent of every choice of H1 lifting of the same
actual physical boundary value, not just of the selected minimum lift. -/
theorem nativeWeakPhysicalConormal_of_any_lift
    (d : Data) (q : Q) (v : H) (hv : T v = HilbertTraceQuotient.value T q) :
    nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d q =
      ell d.val v := by
  have hq : qmap v = q := HilbertTraceQuotient.value_injective T hv
  rw [← hq]
  exact nativeWeakPhysicalConormal_quotientMap g gE e he hei hGauss ha hs hcoeff hC hρ V hV d v

theorem nativeWeakPhysicalConormal_unique
    (d : Data) (A : Q →L[ℝ] ℝ) (hA : A.comp qmap = ell d.val) :
    A = nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d := by
  apply ContinuousLinearMap.ext
  intro q
  have h := congrArg (fun L : H →L[ℝ] ℝ => L (lift q)) hA
  change A (qmap (lift q)) = ell d.val (lift q) at h
  rw [HilbertTraceQuotient.quotientMap_minimumLift] at h
  exact h

/-- Exact bound in the genuine quotient energy dual norm. -/
theorem nativeWeakPhysicalConormal_norm_le (d : Data) :
    ‖nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d‖ ≤
      (8 + ‖nativeRestrictedPotentialForm g Ω V hV‖) * ‖d.val.1‖ +
        ‖LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω d.val.2‖ := by
  have hn : ‖nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d‖ ≤
      ‖ell d.val‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro q
    rw [nativeWeakPhysicalConormalCLM_apply]
    exact ((ell d.val).le_opNorm (lift q)).trans_eq
      (by rw [HilbertTraceQuotient.norm_minimumLift])
  exact hn.trans (nativeWeakEnergySourceDataCLM_apply_norm_le g Ω V hV d.val)

/-- The source coefficient is one and the principal coefficient is
eight. The product data norm is its existing max norm. -/
theorem nativeWeakPhysicalConormalCLM_norm_le :
    @norm _ (by
      exact ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
        (E := Data) (F := Q →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ))
      (nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV) ≤
      9 + ‖nativeRestrictedPotentialForm g Ω V hV‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  change ‖nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d‖ ≤
    (9 + ‖nativeRestrictedPotentialForm g Ω V hV‖) * ‖d‖
  have hu : ‖d.val.1‖ ≤ ‖d‖ := norm_fst_le d.val
  have hF : ‖d.val.2‖ ≤ ‖d‖ := norm_snd_le d.val
  have hFR : ‖LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω d.val.2‖ ≤ ‖d.val.2‖ :=
    norm_Lp_toLp_restrict_le Ω d.val.2
  have hb := nativeWeakPhysicalConormal_norm_le g gE e he hei hGauss ha hs hcoeff hC hρ V hV d
  have hm := mul_le_mul_of_nonneg_left hu
    (show 0 ≤ 8 + ‖nativeRestrictedPotentialForm g Ω V hV‖ by positivity)
  nlinarith only [hb, hm, hFR, hF]

/-- Full weak Green formula for every original global H1 test, using
the same native volume source and potential integrals. The normal term
lies in the actual trace dual; no pointwise normal is asserted. -/
theorem nativeWeakPhysicalConormal_green (d : Data) (v : H) :
    IntegrableOn (fun x => V x * toL2 g.leviCivitaData univ d.val.1 x *
      toL2 g.leviCivitaData univ v x) Ω g.volumeMeasure ∧
    IntegrableOn (fun x => d.val.2 x * toL2 g.leviCivitaData univ v x) Ω g.volumeMeasure ∧
    8 * nativeRestrictedGradientEnergy g Ω d.val.1 v +
        (∫ x in Ω, V x * toL2 g.leviCivitaData univ d.val.1 x *
          toL2 g.leviCivitaData univ v x ∂g.volumeMeasure) =
      (∫ x in Ω, d.val.2 x * toL2 g.leviCivitaData univ v x ∂g.volumeMeasure) +
        nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d (qmap v) := by
  refine ⟨nativeRestrictedPotentialForm_integrable g Ω V hV d.val.1 v,
    nativeRestrictedL2SourceOperator_integrable g Ω d.val.2 v, ?_⟩
  have h := nativeWeakPhysicalConormal_quotientMap g gE e he hei hGauss ha hs hcoeff hC hρ V hV d v
  rw [nativeWeakEnergySourceDataCLM_apply, nativeRestrictedEllipticForm_apply,
    nativeRestrictedPotentialForm_integral, nativeRestrictedL2SourceOperator_apply] at h
  linarith only [h]

/-- The same Green formula for any literal volume representatives of
the original solution, source and test. A.e. identities are used only in
volume integrals. The boundary term remains the proved trace of the H1
element `v`; no restriction of a volume a.e. identity to the sphere is
performed. -/
theorem nativeWeakPhysicalConormal_green_ae
    (d : Data) (v : H) (u f φ : M → ℝ)
    (hu : (toL2 g.leviCivitaData univ d.val.1 : M → ℝ)
      =ᵐ[g.volumeMeasure.restrict Ω] u)
    (hf : (d.val.2 : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω] f)
    (hφ : (toL2 g.leviCivitaData univ v : M → ℝ)
      =ᵐ[g.volumeMeasure.restrict Ω] φ) :
    IntegrableOn (fun x => V x * u x * φ x) Ω g.volumeMeasure ∧
    IntegrableOn (fun x => f x * φ x) Ω g.volumeMeasure ∧
    8 * nativeRestrictedGradientEnergy g Ω d.val.1 v +
        (∫ x in Ω, V x * u x * φ x ∂g.volumeMeasure) =
      (∫ x in Ω, f x * φ x ∂g.volumeMeasure) +
        nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d (qmap v) := by
  have hpot : (fun x => V x * toL2 g.leviCivitaData univ d.val.1 x *
      toL2 g.leviCivitaData univ v x) =ᵐ[g.volumeMeasure.restrict Ω]
        (fun x => V x * u x * φ x) := by
    filter_upwards [hu, hφ] with x hux hφx
    rw [hux, hφx]
  have hsrc : (fun x => d.val.2 x * toL2 g.leviCivitaData univ v x)
      =ᵐ[g.volumeMeasure.restrict Ω] (fun x => f x * φ x) := by
    filter_upwards [hf, hφ] with x hfx hφx
    rw [hfx, hφx]
  obtain ⟨hpi, hsi, hgreen⟩ := nativeWeakPhysicalConormal_green
    g gE e he hei hGauss ha hs hcoeff hC hρ V hV d v
  refine ⟨hpi.congr hpot, hsi.congr hsrc, ?_⟩
  rw [integral_congr_ae hpot, integral_congr_ae hsrc] at hgreen
  exact hgreen

/-- Changing the ambient volume representatives of the same original
solution and source cannot change the constructed weak conormal. -/
theorem nativeWeakPhysicalConormal_representation_independent
    (d₁ d₂ : Data)
    (hu : (toL2 g.leviCivitaData univ d₁.val.1 : M → ℝ) =ᵐ[g.volumeMeasure]
      toL2 g.leviCivitaData univ d₂.val.1)
    (hF : (d₁.val.2 : M → ℝ) =ᵐ[g.volumeMeasure] (d₂.val.2 : M → ℝ)) :
    nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d₁ =
      nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hC hρ V hV d₂ := by
  have hu' : d₁.val.1 = d₂.val.1 := toL2_injective (Lp.ext hu)
  have hF' : d₁.val.2 = d₂.val.2 := Lp.ext hF
  have hd : d₁ = d₂ := Subtype.ext (Prod.ext hu' hF')
  rw [hd]

end Exterior

end EuclideanSphereTrace

#print axioms nativeRestrictedL2SourceOperator_apply
#print axioms nativeRestrictedL2SourceOperator_norm_le
#print axioms nativeRestrictedPotentialForm_integral
#print axioms mem_NativeWeakEllipticDataSpace_iff
#print axioms nativeWeakEllipticDataSpace_complete
#print axioms EuclideanSphereTrace.nativeWeakEnergySource_annihilates_physical_trace_kernel
#print axioms EuclideanSphereTrace.nativeWeakPhysicalConormalCLM
#print axioms EuclideanSphereTrace.nativeWeakPhysicalConormal_factorization
#print axioms EuclideanSphereTrace.nativeWeakPhysicalConormal_of_any_lift
#print axioms EuclideanSphereTrace.nativeWeakPhysicalConormal_unique
#print axioms EuclideanSphereTrace.nativeWeakPhysicalConormal_norm_le
#print axioms EuclideanSphereTrace.nativeWeakPhysicalConormalCLM_norm_le
#print axioms EuclideanSphereTrace.nativeWeakPhysicalConormal_green
#print axioms EuclideanSphereTrace.nativeWeakPhysicalConormal_green_ae
#print axioms EuclideanSphereTrace.nativeWeakPhysicalConormal_representation_independent

end Yamabe3.Analysis
