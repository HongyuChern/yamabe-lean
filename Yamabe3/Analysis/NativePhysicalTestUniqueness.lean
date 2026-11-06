import Yamabe3.Analysis.NativePhysicalSourceL2
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Actual L2 physical representatives are identified from all smooth
compact tests on the punctured ball, without restricting a volume null
set to a sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar

theorem nativePhysicalTest_ae_eq_negative {R f : E → ℝ}
    (hR : MemLp R 2 (volume.restrict (Metric.ball 0 1 \ {(0:E)})))
    (hf : MemLp f 2 (volume.restrict (Metric.ball 0 1 \ {(0:E)})))
    (he : ∀φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ⊆Metric.ball 0 1 \ {(0:E)} →
      (∫x in Metric.ball 0 1 \ {(0:E)},R x*φ x)= -(∫x in Metric.ball 0 1 \ {(0:E)},f x*φ x)) :
    R=ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})] (fun x => -f x) := by
  let O := Metric.ball 0 1 \ {(0:E)}
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have hsum : LocallyIntegrableOn (fun x => R x+f x) O (volume.restrict O) :=
    ((hR.add hf).locallyIntegrable (by norm_num)).locallyIntegrableOn O
  have hz := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero hsum (fun φ hφ hc hs => by
    have hp : MemLp φ 2 (volume.restrict O) := (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
    have hRp := hR.integrable_mul hp
    have hfp := hf.integrable_mul hp
    change (∫x in O,φ x*(R x+f x))=0
    have hn := he φ hφ hc hs
    calc
      _ = ∫x in O,R x*φ x+f x*φ x := by congr 1;funext x;ring
      _ = (∫x in O,R x*φ x)+(∫x in O,f x*φ x) := integral_add hRp hfp
      _ = 0 := by rw [hn];ring)
  filter_upwards [hz,ae_restrict_mem hO.measurableSet] with x hx hO
  exact eq_neg_of_add_eq_zero_left (hx hO)

#print axioms nativePhysicalTest_ae_eq_negative
end Yamabe3.Analysis.SpherePolar
