import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndPhysicalL2
import Yamabe3.Analysis.Cylinder.NativeCylinderHilbertNorm
import Yamabe3.Analysis.UniformElliptic.HalfEndAnnularMeasure

/-! Literal scale-shifts of the same native field. The time translation
and factor exp(2s) are proved to be the physical exp(3s/2) dilation.
The shell bound is uniform in s and uses the original exp(-2t) decay. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology RealInnerProductSpace ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Delaunay SphereSpectrum UniformElliptic

def weightedCylinderShift (s : ℝ) (w : ℝ × S → ℝ) (p : ℝ × S) : ℝ :=
  Real.exp (2*s) * w (p.1+s,p.2)

theorem cylinderLift_weightedCylinderShift (s : ℝ) (w : ℝ × S → ℝ) (x : E) :
    cylinderLift (weightedCylinderShift s w) x =
      Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x) := by
  by_cases hx : x = 0
  · subst x
    simp only [smul_zero,cylinderLift_zero,mul_zero]
  · let y : puncturedSpace := ⟨x,by change x ≠ 0; exact hx⟩
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy : ‖x‖ • (sphereDirection y : E) = x := norm_smul_sphereDirection y
    conv_lhs => rw [← hy]
    conv_rhs => rw [← hy]
    rw [smul_smul,cylinderLift_smul _ hn,cylinderLift_smul _ (mul_pos (Real.exp_pos _) hn),
      radialScale_mul_positive (Real.exp_pos _) hn,radialScale_exp_neg,
      Real.log_mul (Real.exp_pos _).ne' hn.ne',Real.log_exp]
    dsimp only [weightedCylinderShift]
    have ht : -(-s+Real.log ‖x‖) = -Real.log ‖x‖+s := by ring
    rw [ht]
    have he : Real.exp (3*s/2)*Real.exp (s/2) = Real.exp (2*s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (3*s/2)*Real.exp (s/2))*radialScale ‖x‖*w (-Real.log ‖x‖+s,sphereDirection y) := by rw [he]; ring
      _ = _ := by ring

theorem weightedCylinderShift_measurable (s : ℝ) {w : ℝ × S → ℝ} (hw : Measurable w) :
    Measurable (weightedCylinderShift s w) :=
  measurable_const.mul (hw.comp ((measurable_fst.add_const s).prodMk measurable_snd))

theorem weightedCylinderShift_representation (s : ℝ) {U : ℝ → AngularL2} {w : ℝ × S → ℝ}
    (hae : ∀ t, (fun θ => w (t,θ)) =ᵐ[angularVolume] (U t : S → ℝ)) :
    ∀ t, (fun θ => weightedCylinderShift s w (t,θ)) =ᵐ[angularVolume]
      ((Real.exp (2*s) • U (t+s) : AngularL2) : S → ℝ) := by
  intro t
  have hs := (ae_restrict_iff' MeasurableSet.univ).mp
    (Lp.coeFn_smul (Real.exp (2*s)) (U (t+s)))
  filter_upwards [hae (t+s),hs] with θ hθ hsm
  change Real.exp (2*s) * w (t+s,θ) = _
  rw [hθ]
  simpa only [Pi.smul_apply,smul_eq_mul] using (hsm (mem_univ θ)).symm

theorem weighted_curve_decay {U : ℝ → AngularL2} {B : ℝ}
    (hb : ∀ t, ‖U t‖ ≤ Real.exp (-2*t)*B) (s t : ℝ) :
    ‖Real.exp (2*s) • U (t+s)‖ ≤ Real.exp (-2*t)*B := by
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (2*s)*(Real.exp (-2*(t+s))*B) :=
      mul_le_mul_of_nonneg_left (hb (t+s)) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc,← Real.exp_add]; congr 2 <;> ring

theorem weighted_lift_shell_square_bound
    {U : ℝ → AngularL2} (hU : Continuous U) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t,θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    (B : ℝ) (hb : ∀ t, ‖U t‖ ≤ Real.exp (-2*t)*B) (s a b : ℝ) :
    MemLp (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) 2
      (volume.restrict (cylinderShell a b)) ∧
    (∫ x in cylinderShell a b, (Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x))^2) ≤
      (∫ t in Icc a b, Real.exp (-6*t))*B^2 := by
  let W := weightedCylinderShift s w
  let Us (t : ℝ) : AngularL2 := Real.exp (2*s) • U (t+s)
  have hc : Continuous Us := by
    dsimp only [Us]
    exact (hU.comp (continuous_id.add_const s)).const_smul (Real.exp (2*s))
  have hm : Measurable W := weightedCylinderShift_measurable s hw
  have he : ∀ t, (fun θ => W (t,θ)) =ᵐ[angularVolume] (Us t : S → ℝ) :=
    weightedCylinderShift_representation s hae
  have hL := memLp_cylinderLift_on_shell hm a b (native_joint_memLp_interval hc hm he a b)
  have hid : cylinderLift W = fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x) :=
    funext (cylinderLift_weightedCylinderShift s w)
  refine ⟨hid ▸ hL,?_⟩
  change (∫ x in cylinderShell a b, ((fun y => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • y)) x)^2) ≤ _
  rw [← hid,integral_cylinderLift_sq_shell_eq hc hm he,← integral_mul_const]
  apply setIntegral_mono_on
    (((show Continuous (fun t : ℝ => Real.exp (-2*t)) by fun_prop).mul (hc.norm.pow 2)).integrableOn_Icc)
    ((show Continuous (fun t : ℝ => Real.exp (-6*t)*B^2) by fun_prop).integrableOn_Icc) measurableSet_Icc
  intro t ht
  calc
    _ ≤ Real.exp (-2*t)*(Real.exp (-2*t)*B)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (weighted_curve_decay hb s t) 2) (Real.exp_pos _).le
    _ = (Real.exp (-2*t)*Real.exp (-2*t)*Real.exp (-2*t))*B^2 := by ring
    _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 2 <;> ring

#print axioms cylinderLift_weightedCylinderShift
#print axioms weightedCylinderShift_representation
#print axioms weighted_curve_decay
#print axioms weighted_lift_shell_square_bound
end Yamabe3.Analysis.SpherePolar
