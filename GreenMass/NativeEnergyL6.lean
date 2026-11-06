import Yamabe3.Analysis.YamabeCoercivity
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# The actual native H1 completion embeds in L6 under true Yamabe positivity

This is the legal replacement for an unavailable continuous correction in
the dipole problem. The genuine Yamabe energy bounds the L6 norm of actual
smooth energy tests; the map extends to the retained completion, and its
image is proved to represent the same function as the native L2 map.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory UniformSpace Filter
open scoped Manifold ContDiff Topology InnerProductSpace

local instance : Fact (1 ≤ (6 : ENNReal)) := ⟨by norm_num⟩

namespace GreenMass.NativeEnergyL6

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Analysis

section FiniteMeasure

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def sixToTwoLinear : Lp ℝ 6 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (memLp_two_of_six (Lp.memLp f)).toLp f
  map_add' f h := by
    apply Lp.ext
    filter_upwards [(memLp_two_of_six (Lp.memLp (f + h))).coeFn_toLp,
      (memLp_two_of_six (Lp.memLp f)).coeFn_toLp,
      (memLp_two_of_six (Lp.memLp h)).coeFn_toLp,
      Lp.coeFn_add f h,
      Lp.coeFn_add ((memLp_two_of_six (Lp.memLp f)).toLp f)
        ((memLp_two_of_six (Lp.memLp h)).toLp h)] with x hsum hf hh hadd htarget
    rw [hsum, hadd, htarget]
    simp only [Pi.add_apply, hf, hh]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_two_of_six (Lp.memLp (c • f))).coeFn_toLp,
      (memLp_two_of_six (Lp.memLp f)).coeFn_toLp,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((memLp_two_of_six (Lp.memLp f)).toLp f)] with x hcf hf hsm htarget
    simp only [RingHom.id_apply]
    rw [hcf, hsm, htarget]
    simp only [Pi.smul_apply, hf]

theorem sixToTwoLinear_bound (f : Lp ℝ 6 μ) :
    ‖sixToTwoLinear μ f‖ ≤ (μ univ).toReal ^ (1 / 3 : ℝ) * ‖f‖ := by
  change ‖(memLp_two_of_six (Lp.memLp f)).toLp f‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  simpa only [mul_comm] using toReal_eLpNorm_two_le_six (Lp.memLp f)

def sixToTwo : Lp ℝ 6 μ →L[ℝ] Lp ℝ 2 μ :=
  (sixToTwoLinear μ).mkContinuous ((μ univ).toReal ^ (1 / 3 : ℝ))
    (sixToTwoLinear_bound μ)

theorem sixToTwo_ae (f : Lp ℝ 6 μ) : (sixToTwo μ f : X → ℝ) =ᵐ[μ] f :=
  (memLp_two_of_six (Lp.memLp f)).coeFn_toLp

end FiniteMeasure

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

-- Reuse the canonical existing normed-space instances explicitly, avoiding
-- a nested continuous-bilinear-map elaboration ambiguity in the fixed baseline.
local instance (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (EnergyTest g.leviCivitaData univ) := inferInstance
local instance (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance

omit [CompactSpace M] [ConnectedSpace M] in
theorem test_memLp_six (g : RiemannianMetric 3 M)
    (f : EnergyTest g.leviCivitaData univ) : MemLp (f : M → ℝ) 6 g.volumeMeasure :=
  f.smooth.continuous.memLp_of_hasCompactSupport f.hasCompactSupport

def testToL6Linear (g : RiemannianMetric 3 M) :
    EnergyTest g.leviCivitaData univ →ₗ[ℝ] Lp ℝ 6 g.volumeMeasure where
  toFun f := (test_memLp_six g f).toLp f
  map_add' f h := by
    apply Lp.ext
    filter_upwards [(test_memLp_six g (f + h)).coeFn_toLp,
      (test_memLp_six g f).coeFn_toLp, (test_memLp_six g h).coeFn_toLp,
      Lp.coeFn_add ((test_memLp_six g f).toLp f) ((test_memLp_six g h).toLp h)]
      with x hsum hf hh hadd
    rw [hsum, hadd]
    change f x + h x = ((test_memLp_six g f).toLp f) x + ((test_memLp_six g h).toLp h) x
    rw [hf, hh]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(test_memLp_six g (c • f)).coeFn_toLp,
      (test_memLp_six g f).coeFn_toLp,
      Lp.coeFn_smul c ((test_memLp_six g f).toLp f)] with x hcf hf hsm
    simp only [RingHom.id_apply]
    rw [hcf, hsm]
    change c * f x = c * ((test_memLp_six g f).toLp f) x
    rw [hf]

omit [CompactSpace M] [ConnectedSpace M] in
theorem testToL6_norm_sq (g : RiemannianMetric 3 M)
    (f : EnergyTest g.leviCivitaData univ) :
    ‖testToL6Linear g f‖ ^ 2 = (∫ x, |f x| ^ 6 ∂g.volumeMeasure) ^ (1 / 3 : ℝ) := by
  have hf := test_memLp_six g f
  change ‖hf.toLp (f : M → ℝ)‖ ^ 2 = _
  rw [Lp.norm_toLp, toReal_eLpNorm hf.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num [Real.norm_eq_abs, Real.rpow_natCast]
  rw [← Real.rpow_mul_natCast (integral_nonneg (fun x => pow_nonneg (abs_nonneg (f x)) 6))]
  norm_num

theorem testToL6_norm_bound (g : RiemannianMetric 3 M)
    (hY : 0 < Yamabe3.Target.yamabeConstant g) (f : EnergyTest g.leviCivitaData univ) :
    ‖testToL6Linear g f‖ ≤
      Real.sqrt (‖closedYamabeForm g‖ / Yamabe3.Target.yamabeConstant g) * ‖f‖ := by
  have henergy : Yamabe3.Target.yamabeConstant g * ‖testToL6Linear g f‖ ^ 2 ≤
      closedYamabeForm g (f : H1Zero g.leviCivitaData univ)
        (f : H1Zero g.leviCivitaData univ) := by
    by_cases hz : (f : M → ℝ) = 0
    · have hf : f = 0 := Subtype.ext hz
      rw [hf, Completion.coe_zero]
      simp
    · rw [testToL6_norm_sq, closedYamabeForm_coe]
      exact Yamabe3.Target.energy_lower_bound g hY f.smooth hz
  have hbound := (closedYamabeForm g).le_opNorm₂
    (f : H1Zero g.leviCivitaData univ) (f : H1Zero g.leviCivitaData univ)
  simp only [Completion.norm_coe] at hbound
  have hsquare : ‖testToL6Linear g f‖ ^ 2 ≤
      (‖closedYamabeForm g‖ / Yamabe3.Target.yamabeConstant g) * ‖f‖ ^ 2 := by
    have hle := henergy.trans ((le_abs_self _).trans hbound)
    calc
      _ ≤ (‖closedYamabeForm g‖ * ‖f‖ ^ 2) / Yamabe3.Target.yamabeConstant g :=
        (le_div_iff₀ hY).mpr (by convert hle using 1 <;> ring)
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
  rw [mul_pow, Real.sq_sqrt (div_nonneg (norm_nonneg (closedYamabeForm g)) hY.le)]
  exact hsquare

def toL6 (g : RiemannianMetric 3 M) (hY : 0 < Yamabe3.Target.yamabeConstant g) :
    H1Zero g.leviCivitaData univ →L[ℝ] Lp ℝ 6 g.volumeMeasure :=
  ((testToL6Linear g).mkContinuous
    (Real.sqrt (‖closedYamabeForm g‖ / Yamabe3.Target.yamabeConstant g))
    (testToL6_norm_bound g hY)).extend Completion.toComplL

@[simp] theorem toL6_coe (g : RiemannianMetric 3 M)
    (hY : 0 < Yamabe3.Target.yamabeConstant g) (f : EnergyTest g.leviCivitaData univ) :
    toL6 g hY (f : H1Zero g.leviCivitaData univ) = (test_memLp_six g f).toLp f := by
  exact ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe (EnergyTest g.leviCivitaData univ)) f

/-- The L6 image is the same native function as the existing L2 realization
of the energy element. This prevents substituting an unrelated completion. -/
theorem toL6_ae_toL2 (g : RiemannianMetric 3 M)
    (hY : 0 < Yamabe3.Target.yamabeConstant g) (u : H1Zero g.leviCivitaData univ) :
    (toL6 g hY u : M → ℝ) =ᵐ[g.volumeMeasure] toL2 g.leviCivitaData univ u := by
  let : IsFiniteMeasure g.volumeMeasure :=
    ⟨g.volumeMeasure_lt_top_of_isCompact isCompact_univ⟩
  have hsame (w : H1Zero g.leviCivitaData univ) :
      sixToTwo g.volumeMeasure (toL6 g hY w) = toL2 g.leviCivitaData univ w := by
    induction w using Completion.induction_on with
    | hp =>
      apply isClosed_eq <;> fun_prop
    | ih f =>
      rw [toL6_coe, toL2_coe]
      apply Lp.ext
      filter_upwards [sixToTwo_ae g.volumeMeasure ((test_memLp_six g f).toLp f),
        (test_memLp_six g f).coeFn_toLp, f.memLp.coeFn_toLp] with x hst hf6 hf2
      rw [hst, hf6]
      exact hf2.symm
  have he := sixToTwo_ae g.volumeMeasure (toL6 g hY u)
  rw [hsame u] at he
  exact he.symm

/-- Every actual completed energy element has a genuine L6 representative. -/
theorem native_energy_memLp_six (g : RiemannianMetric 3 M)
    (hY : 0 < Yamabe3.Target.yamabeConstant g) (u : H1Zero g.leviCivitaData univ) :
    MemLp (toL2 g.leviCivitaData univ u : M → ℝ) 6 g.volumeMeasure :=
  (Lp.memLp (toL6 g hY u)).ae_eq (toL6_ae_toL2 g hY u)

#print axioms testToL6_norm_bound
#print axioms toL6_ae_toL2
#print axioms native_energy_memLp_six

end GreenMass.NativeEnergyL6
