import Yamabe3.Analysis.NativeChartCollarTail
import Yamabe3.Analysis.NativeChartBoundaryCutoffEnergy
import Yamabe3.Analysis.NativePhysicalCanonicalSphereTrace

/-!
# Actual L2 mass and completed boundary-layer energy

The L2 term below uses the existing representative map from the original
native energy completion, followed by restriction of the actual native
volume. Its value is the literal volume integral of that representative.
The boundary term is the canonical trace already constructed in the
actual induced sphere area; it is not an arbitrary map with a trace axiom.

The smooth boundary-layer estimate extends to the same completed element
by density and continuity. For zero canonical trace, the scaled L2 mass
in the genuine shrinking chart collars tends to zero by the previously
proved restricted-gradient tail theorem. No restriction of an ambient
almost-everywhere identity to the sphere is used.

These are estimates for a prospective one-sided H1 restriction. This
file does not assert that the global trace kernel equals a domain H1-zero
space, and does not assume or conclude a weak Green identity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open Set Filter MeasureTheory UniformSpace
open scoped Topology ContDiff Manifold InnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

private theorem realL2_norm_sq_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} (u : Lp ℝ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  ext x
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def restrictedEnergyLimitH1NormedSpace (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] restrictedEnergyLimitH1NormedSpace

/-- Restrict the existing representative of the same H1 element using
the original metric's native volume. -/
def nativeRestrictedL2CLM (g : RiemannianMetric 3 M) (Ω : Set M) :
    H1Zero g.leviCivitaData univ →L[ℝ] Lp ℝ 2 (g.volumeMeasure.restrict Ω) :=
  (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω).comp
    (toL2 g.leviCivitaData univ)

/-- The restricted norm is the genuine integral of the original L2
representative, independently of the representative selected by Lp. -/
theorem nativeRestrictedL2CLM_norm_sq
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (w : H1Zero g.leviCivitaData univ) :
    ‖nativeRestrictedL2CLM g Ω w‖ ^ 2 =
      ∫ x in Ω, (toL2 g.leviCivitaData univ w x) ^ 2 ∂g.volumeMeasure := by
  rw [realL2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ Ω
    (toL2 g.leviCivitaData univ w)] with x hx
  exact congrArg (fun t : ℝ => t ^ 2) hx

/-- Smooth elements retain their literal native volume mass. -/
theorem nativeRestrictedL2CLM_norm_sq_coe
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (φ : EnergyTest g.leviCivitaData univ) :
    ‖nativeRestrictedL2CLM g Ω (φ : H1Zero g.leviCivitaData univ)‖ ^ 2 =
      ∫ x in Ω, φ x ^ 2 ∂g.volumeMeasure := by
  rw [nativeRestrictedL2CLM_norm_sq, toL2_coe]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae φ.memLp.coeFn_toLp] with x hx
  exact congrArg (fun t : ℝ => t ^ 2) hx

/-- L2 mass of the same native H1 element vanishes on any measurable
sequence of domains eventually avoiding almost every actual point. -/
theorem nativeRestrictedL2CLM_norm_sq_tendsto_zero
    (g : RiemannianMetric 3 M) (Ω : ℕ → Set M)
    (hΩ : ∀ n, MeasurableSet (Ω n))
    (hpoint : ∀ᵐ x ∂g.volumeMeasure, ∀ᶠ n in atTop, x ∉ Ω n)
    (w : H1Zero g.leviCivitaData univ) :
    Tendsto (fun n => ‖nativeRestrictedL2CLM g (Ω n) w‖ ^ 2) atTop (𝓝 0) := by
  let u := toL2 g.leviCivitaData univ w
  have hi : Integrable (fun x => u x ^ 2) g.volumeMeasure := (Lp.memLp u).integrable_sq
  have hlim : Tendsto
      (fun n => ∫ x, (Ω n).indicator (fun y => u y ^ 2) x ∂g.volumeMeasure)
      atTop (𝓝 (∫ _x : M, (0 : ℝ) ∂g.volumeMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖u x ^ 2‖)
    · intro n
      exact hi.aestronglyMeasurable.indicator (hΩ n)
    · exact hi.norm
    · intro n
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ Ω n
        · simp [hx]
        · simp only [indicator_of_notMem hx, norm_zero]
          exact norm_nonneg _
    · filter_upwards [hpoint] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with n hn
      simp [hn]
  simpa only [nativeRestrictedL2CLM_norm_sq, integral_indicator (hΩ _),
    integral_zero, u] using hlim

namespace EuclideanSphereTrace

open SpherePolar NativeChartSphereMetric

variable (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
  (e : OpenPartialHomeomorph E M)
  (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  {a A : ℝ} (ha : 0 < a)
  (hKs : sphereTraceAnnulus a (2 * a) ⊆ e.source)
  (hcoeff : ∀ x ∈ sphereTraceAnnulus a (2 * a),
    gE.euclideanCoefficients x = g.pullbackCoefficients e x)
  (hGauss : ∀ x ∈ sphereTraceAnnulus a (2 * a), ∀ v : E,
    gE.inner x x v = inner ℝ x v)
  (hA : 0 ≤ A)
  (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (a • (θ : E)) ≤ A)

private theorem inner_collar_radius_mem {a : ℝ} (ha : 0 < a) : a ∈ Icc a (2 * a) :=
  ⟨le_rfl, by linarith only [ha]⟩

private theorem collar_radius_lt {a : ℝ} (ha : 0 < a) : a < 2 * a := by linarith only [ha]

local notation "hr" => inner_collar_radius_mem ha
local notation "hab" => collar_radius_lt ha
local notation "hθ" => (fun θ : S => radial_mem_sphereTraceAnnulus ha hr θ)
local notation "T" => nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hA
  (fun θ => hcoeff _ (hθ θ)) (fun θ => hGauss _ (hθ θ)) hρ

/-- The native smooth boundary-layer estimate extends to every original
H1 element and to its canonical trace in the actual sphere area. The
constant precedes the collar thickness and the completed element. -/
theorem exists_native_completed_boundary_layer_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → 2 * δ ≤ a →
      ∀ w : H1Zero g.leviCivitaData univ,
      δ⁻¹ ^ 2 * ‖nativeRestrictedL2CLM g
        (e '' sphereTraceAnnulus a (a + 2 * δ)) w‖ ^ 2 ≤
        C * (δ⁻¹ * ‖T w‖ ^ 2 + nativeRestrictedGradientEnergy g
          (e '' sphereTraceAnnulus a (a + 2 * δ)) w w) := by
  obtain ⟨C, hC, hbound⟩ := exists_native_chart_boundary_layer_energy_bound
    g gE e he hei ha hKs hcoeff hGauss (fun θ => hKs (hθ θ))
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδa w
  induction w using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih φ =>
    rw [nativeRestrictedL2CLM_norm_sq_coe, nativeRestrictedGradientEnergy_coe]
    have htrace : ‖T (φ : H1Zero g.leviCivitaData univ)‖ ^ 2 =
        ∫ θ : S, φ (e (a • (θ : E))) ^ 2
          ∂(chartRadiusMetric g e he hei a ha.ne' (fun θ => hKs (hθ θ))).volumeMeasure := by
      rw [realL2_norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [nativePhysicalSphereTraceCLM_coe_ae
        g gE e he hei ha hab hr hKs hA
        (fun θ => hcoeff _ (hθ θ)) (fun θ => hGauss _ (hθ θ)) hρ φ] with θ hθeq
      exact congrArg (fun t : ℝ => t ^ 2) hθeq
    rw [htrace]
    exact hbound δ hδ hδa φ

/-- For the actual zero canonical trace, only the shrinking native
gradient energy remains. The global H1 element may be nonzero inside
the deleted ball; no false kernel/domain identification is made. -/
theorem exists_native_zero_trace_boundary_layer_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → 2 * δ ≤ a →
      ∀ w : H1Zero g.leviCivitaData univ, T w = 0 →
      δ⁻¹ ^ 2 * ‖nativeRestrictedL2CLM g
        (e '' sphereTraceAnnulus a (a + 2 * δ)) w‖ ^ 2 ≤
        C * nativeRestrictedGradientEnergy g
          (e '' sphereTraceAnnulus a (a + 2 * δ)) w w := by
  obtain ⟨C, hC, hbound⟩ := exists_native_completed_boundary_layer_energy_bound
    g gE e he hei ha hKs hcoeff hGauss hA hρ
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδa w hw
  simpa only [hw, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
    using hbound δ hδ hδa w

/-- Scaled collar mass of the same zero-trace completed element tends
to zero. This uses the original volume, the actual canonical boundary
trace, and the actual shrinking-domain gradient energy throughout. -/
theorem native_zero_trace_scaled_collar_mass_tendsto_zero
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδa : ∀ n, 2 * δ n ≤ a) (hδ : Tendsto δ atTop (𝓝 0))
    (w : H1Zero g.leviCivitaData univ) (hw : T w = 0) :
    Tendsto (fun n => (δ n)⁻¹ ^ 2 * ‖nativeRestrictedL2CLM g
      (e '' sphereTraceAnnulus a (a + 2 * δ n)) w‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_native_zero_trace_boundary_layer_energy_bound
    g gE e he hei ha hKs hcoeff hGauss hA hρ
  have hgrad := native_chart_collar_gradient_energy_tendsto_zero g e he hei
    ha hKs δ hδa hδ w
  apply squeeze_zero (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun n => hbound (δ n) (hδpos n) (hδa n) w hw)
  simpa only [mul_zero] using hgrad.const_mul C

end EuclideanSphereTrace

#print axioms nativeRestrictedL2CLM_norm_sq
#print axioms nativeRestrictedL2CLM_norm_sq_coe
#print axioms nativeRestrictedL2CLM_norm_sq_tendsto_zero
#print axioms EuclideanSphereTrace.exists_native_completed_boundary_layer_energy_bound
#print axioms EuclideanSphereTrace.exists_native_zero_trace_boundary_layer_energy_bound
#print axioms EuclideanSphereTrace.native_zero_trace_scaled_collar_mass_tendsto_zero

end Yamabe3.Analysis
