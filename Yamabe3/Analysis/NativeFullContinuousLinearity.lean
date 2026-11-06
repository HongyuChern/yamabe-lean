import Yamabe3.Analysis.NativeFullContinuousH4
import Yamabe3.Analysis.NativeFullPairLinearity

/-! Actual source linearity survives completion, a.e.-compatible collar
extension and continuous representative selection. Uniqueness comes from
volume full support, not from a claimed linearity of arbitrary choices. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E) 1 \ {(0:E)}
local notation "X" => (E→ℝ) × (E→ℝ)

theorem continuous_full_completion_extension_linear
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (p : DelaunayPhaseData κ)
    (G : X →ₗ[ℝ] (E → ℝ))
    (hGAE : ∀u v:X,u.1 =ᵐ[volume] v.1 → u.2 =ᵐ[volume] v.2 → G u =ᵐ[volume] G v)
    (F : HalfEndPhysicalH2SourceGraph → E → ℝ) (hFc : ∀ f, Continuous (F f))
    (hF : ∀ f, F f =ᵐ[volume] G (fullModelCompletionPair hκ0 hκ1 p f)) :
    (∀ f g, F (f+g) = F f+F g) ∧ (∀ (c : ℝ) f, F (c • f) = c • F f) := by
  let Z (f : HalfEndPhysicalH2SourceGraph) : X := fullModelCompletionPair hκ0 hκ1 p f
  constructor
  · intro f g
    have hg : G (Z (f+g)) =ᵐ[volume] G (Z f)+G (Z g) := by
      have hh:=fullModelCompletionPair_add_ae hκ0 hκ1 p f g
      simpa only [map_add] using hGAE (Z (f+g)) (Z f+Z g) hh.1 (Eventually.of_forall (fun x=>congrFun hh.2 x))
    have he : F (f+g) =ᵐ[volume] F f+F g :=
      (hF (f+g)).trans (hg.trans ((hF f).add (hF g)).symm)
    have he' : F (f+g) =ᵐ[volume.restrict univ] F f+F g := by simpa only [Measure.restrict_univ] using he
    have hh := Measure.eqOn_open_of_ae_eq he' isOpen_univ (hFc (f+g)).continuousOn ((hFc f).add (hFc g)).continuousOn
    exact funext (fun x => hh (mem_univ x))
  · intro c f
    have hg : G (Z (c • f)) =ᵐ[volume] c • G (Z f) := by
      have hh:=fullModelCompletionPair_smul_ae hκ0 hκ1 p c f
      simpa only [map_smul] using hGAE (Z (c • f)) (c • Z f) hh.1 (Eventually.of_forall (fun x=>congrFun hh.2 x))
    have hf : c • F f =ᵐ[volume] c • G (Z f) := by
      filter_upwards [hF f] with x hx
      exact congrArg (fun t : ℝ => c*t) hx
    have he : F (c • f) =ᵐ[volume.restrict univ] c • F f := by
      simpa only [Measure.restrict_univ] using (hF (c • f)).trans (hg.trans hf.symm)
    have hh := Measure.eqOn_open_of_ae_eq he isOpen_univ (hFc (c • f)).continuousOn ((hFc f).const_smul c).continuousOn
    exact funext (fun x => hh (mem_univ x))

#print axioms continuous_full_completion_extension_linear
end Yamabe3.Analysis.UniformElliptic
