import Yamabe3.Analysis.NativeHalfEndSourceChart
import PoincareLib.Geometry.Manifold.SmoothDomain.HalfSpaceChart

/-! Actual flattening charts at every point of the physical unit sphere.
Their physical targets lie in the fixed source collar, avoid the puncture,
and flatten the punctured unit ball to the positive first half-space. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold InnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_unitSphere_flattening_chart (a : E) (ha : ‖a‖ = 1) :
    ∃ e : OpenPartialHomeomorph E E,
      a ∈ e.target ∧ e.target ⊆ halfEndSourceAnnulus ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      (∀ x ∈ e.source, e x ∈ (Metric.ball (0 : E) 1 \ {(0 : E)}) ↔ 0 < x 0) ∧
      e.symm a 0 = 0 := by
  let f : E → ℝ := fun x => 1 - ‖x‖^2
  have hf : ContDiff ℝ ∞ f := contDiff_const.sub (contDiff_norm_sq ℝ)
  have hreg : Function.Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f a) := by
    rw [mfderiv_eq_fderiv]
    change ∀ r : ℝ, ∃ v : E, fderiv ℝ f a v = r
    intro r
    refine ⟨(-r/2) • a, ?_⟩
    change fderiv ℝ (fun x : E => 1 - ‖x‖^2) a ((-r/2) • a) = r
    rw [fderiv_const_sub, fderiv_norm_sq_apply]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.map_smul, innerSL_apply_apply, real_inner_self_eq_norm_sq, ha, one_pow, smul_eq_mul]
    ring
  obtain ⟨p, hap, hp, hpi, hfirst, -⟩ := Poincare.Manifold.exists_normalized_regular_point_chart
    (n := 2) (by simp : Module.finrank ℝ E = 2+1) hf.contMDiff a 0 hreg
  let q := p.restrOpen halfEndSourceAnnulus halfEndSourceAnnulus_isOpen
  have haW : a ∈ halfEndSourceAnnulus := by
    change (3/4 : ℝ) < ‖a‖ ∧ ‖a‖ < 3/2
    rw [ha]; norm_num
  have haq : a ∈ q.source := ⟨hap, haW⟩
  refine ⟨q.symm, haq, (fun x hx => hx.2), hpi.mono (fun x hx => hx.1),
    hp.mono (fun x hx => hx.1), ?_, ?_⟩
  · intro x hx
    have hxq := q.map_target hx
    have hxW : q.symm x ∈ halfEndSourceAnnulus := hxq.2
    have hx0 : q.symm x ≠ 0 := by
      intro he
      change (3/4 : ℝ) < ‖q.symm x‖ ∧ ‖q.symm x‖ < 3/2 at hxW
      norm_num [he] at hxW
    have hxcoord : x 0 = 1 - ‖q.symm x‖^2 := by
      have hh := hfirst (q.symm x) hxq.1
      have hid : p (q.symm x) = x := q.right_inv hx
      rw [hid] at hh
      simpa only [f, sub_zero] using hh
    simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_singleton_iff, hx0, not_false_eq_true, and_true]
    rw [hxcoord]
    constructor <;> intro h <;> nlinarith [norm_nonneg (q.symm x)]
  · have hh := hfirst a hap
    change p a 0 = 0
    simpa only [f, ha, one_pow, sub_self, sub_zero] using hh

#print axioms exists_unitSphere_flattening_chart
end Yamabe3.Analysis.UniformElliptic
