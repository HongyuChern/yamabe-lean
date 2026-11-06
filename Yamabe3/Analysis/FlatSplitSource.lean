import Yamabe3.Analysis.FlatTransmissionBothSides
import Yamabe3.Analysis.NormalReflectionSobolevNorm

/-! Physical two-piece sources are encoded without identifying their
values on the interface. Reflection only re-encodes the negative piece. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.BoundaryTangential
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def flatSplitSource (f g : E → ℝ) (x : E) : ℝ :=
  if 0<x 0 then f x else if x 0<0 then g x else 0

theorem normalReflection_involutive :
    Function.Involutive (normalScaling (d:=d) (-1) (by norm_num)) := by
  intro x
  ext i
  by_cases hi : i=0 <;> simp [normalFactor,hi]

theorem twoSidedHalfSource_reflection_eq (f g : E → ℝ) :
    twoSidedHalfSource f (fun x => g (normalScaling (-1) (by norm_num) x))=flatSplitSource f g := by
  funext x
  by_cases hp : 0<x 0
  · rw [twoSidedHalfSource_positive f _ hp]
    simp [flatSplitSource,hp]
  · by_cases hn : x 0<0
    · rw [twoSidedHalfSource_negative f _ hn,normalReflection_involutive]
      simp [flatSplitSource,hp,hn]
    · have hxp : x∉halfSpace d := hp
      have hxr : scaledReflect 1 (by norm_num) x∉halfSpace d := by
        change ¬0<scaledReflect 1 (by norm_num) x 0
        rw [scaledReflect_normal]
        simp only [neg_one_mul,neg_pos]
        exact hn
      simp only [twoSidedHalfSource,Pi.add_apply,indicator_of_notMem hxp,
        reflectedSample,indicator_of_notMem hxr,add_zero,flatSplitSource,if_neg hp,if_neg hn]

theorem flatSplitSource_congr_on {O : Set E} {f g F G : E → ℝ}
    (hf : EqOn f F O) (hg : EqOn g G O) : EqOn (flatSplitSource f g) (flatSplitSource F G) O := by
  intro x hx
  simp only [flatSplitSource,hf hx,hg hx]

#print axioms normalReflection_involutive
#print axioms twoSidedHalfSource_reflection_eq
#print axioms flatSplitSource_congr_on
end Yamabe3.Analysis.UniformElliptic
