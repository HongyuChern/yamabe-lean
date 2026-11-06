import Yamabe3.Analysis.WeakDilationNorm
import Yamabe3.Analysis.NativeAllScaleH4

/-! Exact critical three-dimensional dilation factors, used to keep
the third and fourth Taylor-remainder derivative rows bounded without
assuming pointwise bounds for fourth derivatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem dilationL2Factor_three_exp (s:ℝ) :
    dilationL2Factor 3 (Real.exp (-s))=ENNReal.ofReal (Real.exp (3*s/2)) := by
  have he:Real.exp (-s)^3=Real.exp (-3*s) := by
    rw [pow_three,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hi:(Real.exp (-3*s))⁻¹=Real.exp (3*s) := by
    rw [←Real.exp_neg]
    congr 1
    ring
  unfold dilationL2Factor
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  rw [he,hi,abs_of_pos (Real.exp_pos _),ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),←Real.exp_mul]
  congr 1
  congr 1
  ring

theorem weightedPhysicalDilation_jet_norm
    {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) (s:ℝ) (n:ℕ) (x:E3) :
    ‖iteratedFDeriv ℝ n (weightedPhysicalDilation s f) x‖=
      (Real.exp (3*s/2)*Real.exp (-s)^n)*‖iteratedFDeriv ℝ n f (Real.exp (-s) • x)‖ := by
  change ‖iteratedFDeriv ℝ n (Real.exp (3*s/2) • (fun y:E3 => f (Real.exp (-s) • y))) x‖=_
  rw [iteratedFDeriv_const_smul_apply (a:=Real.exp (3*s/2))
    (f:=(fun y:E3 => f (Real.exp (-s) • y)))
    ((hf.comp (contDiff_id.const_smul (Real.exp (-s)))).contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,
    iteratedFDeriv_comp_const_smul (Real.exp (-s)) (hf.of_le (by exact_mod_cast le_top)),
    norm_smul,norm_pow,Real.norm_of_nonneg (Real.exp_pos _).le]
  ring

theorem weightedPhysicalDilation_profile_term
    {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) (s:ℝ) (n:ℕ) (V:Set E3) :
    eLpNorm (fun x:E3 => ‖iteratedFDeriv ℝ n (weightedPhysicalDilation s f) x‖) 2 (volume.restrict V)=
      ENNReal.ofReal (Real.exp (3*s/2)*Real.exp (-s)^n)*
        eLpNorm (fun x:E3 => ‖iteratedFDeriv ℝ n f (Real.exp (-s) • x)‖) 2 (volume.restrict V) := by
  simp_rw [weightedPhysicalDilation_jet_norm hf]
  change eLpNorm ((Real.exp (3*s/2)*Real.exp (-s)^n) •
    (fun x:E3 => ‖iteratedFDeriv ℝ n f (Real.exp (-s) • x)‖)) 2 (volume.restrict V)=_
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal (by positivity)]

#print axioms dilationL2Factor_three_exp
#print axioms weightedPhysicalDilation_jet_norm
#print axioms weightedPhysicalDilation_profile_term
end Yamabe3.Analysis.UniformElliptic
