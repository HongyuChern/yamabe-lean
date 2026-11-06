import Yamabe3.Analysis.NativeContinuousH4Family
import Yamabe3.Analysis.NativeHalfEndCompletionLinearity

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

theorem continuous_completion_extension_linear
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (p : DelaunayPhaseData κ)
    (G : (E → ℝ) →ₗ[ℝ] (E → ℝ))
    (hGAE : ∀ u v : E → ℝ, u =ᵐ[volume] v → G u =ᵐ[volume] G v)
    (F : HalfEndHighH2Source → E → ℝ) (hFc : ∀ f, Continuous (F f))
    (hF : ∀ f, F f =ᵐ[volume] G (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f))) :
    (∀ f g, F (f+g) = F f+F g) ∧ (∀ (c : ℝ) f, F (c • f) = c • F f) := by
  let Z (f : HalfEndHighH2Source) : E → ℝ := toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)
  have hZadd (f g : HalfEndHighH2Source) : Z (f+g) =ᵐ[volume] Z f+Z g := by
    dsimp only [Z,delaunayPhaseCompletion]
    rw [nativeHalfEndH2SourceCompletion_add,map_add]
    simpa only [native_euclideanMetric_volumeMeasure] using Lp.coeFn_add
      (toL2 nativeWeakEuclideanD O (nativeHalfEndH2SourceCompletion hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg p.potential_smooth f))
      (toL2 nativeWeakEuclideanD O (nativeHalfEndH2SourceCompletion hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg p.potential_smooth g))
  have hZsmul (c : ℝ) (f : HalfEndHighH2Source) : Z (c • f) =ᵐ[volume] c • Z f := by
    dsimp only [Z,delaunayPhaseCompletion]
    rw [nativeHalfEndH2SourceCompletion_smul,map_smul]
    simpa only [native_euclideanMetric_volumeMeasure] using Lp.coeFn_smul c
      (toL2 nativeWeakEuclideanD O (nativeHalfEndH2SourceCompletion hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg p.potential_smooth f))
  constructor
  · intro f g
    have hg : G (Z (f+g)) =ᵐ[volume] G (Z f)+G (Z g) := by
      simpa only [map_add] using hGAE _ _ (hZadd f g)
    have he : F (f+g) =ᵐ[volume] F f+F g :=
      (hF (f+g)).trans (hg.trans ((hF f).add (hF g)).symm)
    have he' : F (f+g) =ᵐ[volume.restrict univ] F f+F g := by simpa only [Measure.restrict_univ] using he
    have hh := Measure.eqOn_open_of_ae_eq he' isOpen_univ (hFc (f+g)).continuousOn ((hFc f).add (hFc g)).continuousOn
    exact funext (fun x => hh (mem_univ x))
  · intro c f
    have hg : G (Z (c • f)) =ᵐ[volume] c • G (Z f) := by
      simpa only [map_smul] using hGAE _ _ (hZsmul c f)
    have hf : c • F f =ᵐ[volume] c • G (Z f) := by
      filter_upwards [hF f] with x hx
      exact congrArg (fun t : ℝ => c*t) hx
    have he : F (c • f) =ᵐ[volume.restrict univ] c • F f := by
      simpa only [Measure.restrict_univ] using (hF (c • f)).trans (hg.trans hf.symm)
    have hh := Measure.eqOn_open_of_ae_eq he isOpen_univ (hFc (c • f)).continuousOn ((hFc f).const_smul c).continuousOn
    exact funext (fun x => hh (mem_univ x))

#print axioms continuous_completion_extension_linear
end Yamabe3.Analysis.UniformElliptic
