import Yamabe3.Analysis.NativeCollarGluedDivergence
import Yamabe3.Analysis.NativeCollarJetSobolevBound
import Yamabe3.Analysis.WeakDivergenceH2Estimate
import Yamabe3.Analysis.NativeDelaunayH4Estimate

/-! A bounded H2 estimate for the literal matched field on each fixed
smaller collar domain. The field crosses the sphere; its estimate follows
from its proved weak equation, not from separate one-sided membership. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated

lemma physicalSplitSource_eLpNorm_le (μ : Measure E) {Ω : Set E} (hΩ : MeasurableSet Ω)
    {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    eLpNorm (physicalSplitSource Ω f g) 2 μ≤eLpNorm f 2 μ+eLpNorm g 2 μ := by
  classical
  have he : physicalSplitSource Ω f g=Ω.indicator f+Ωᶜ.indicator g := by
    funext x
    by_cases hx : x∈Ω <;> simp [physicalSplitSource,hx]
  rw [he]
  exact (eLpNorm_add_le (hf.indicator hΩ).aestronglyMeasurable
    (hg.indicator hΩ.compl).aestronglyMeasurable (by norm_num)).trans
    (add_le_add (eLpNorm_indicator_le f) (eLpNorm_indicator_le g))

theorem exists_nativeCollarGlued_H2_bound {W : Set E}
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWD : closure W⊆nativePoissonEntranceCollar) :
    ∃ C : ℝ≥0∞,C≠⊤ ∧ ∀ J K : nativeCollarJetClosure,
      nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K →
      nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K →
      MemWkp 2 2 (nativeCollarGluedFunction J.val.1 K.val.1) W ∧
      iteratedWeakSobolevNorm 2 2 (nativeCollarGluedFunction J.val.1 K.val.1) W≤
        C*(ENNReal.ofReal ‖J‖+ENNReal.ofReal ‖K‖) := by
  obtain ⟨V,hV,hWV,hVD,hVc⟩ := exists_open_between_and_isCompact_closure hWc
    (nativePolarTimeWindow_open (1/2)) hWD
  let B := euclideanPrincipalForm (univ : Set E)
  obtain ⟨C,hC,hb⟩ := exists_weak_divergence_H2_operator_estimate B hV hVc hW hWc hWV
  obtain ⟨M,hM,hm⟩ := exists_weakDivergenceSource_bound hV hVc B.a B.smooth_a
  refine ⟨C*((1+M)*13),by finiteness,?_⟩
  intro J K hv hn
  let u := nativeCollarGluedFunction J.val.1 K.val.1
  have hul := nativeCollarGluedFunction_local_H2 J K hv hn
  have huV := memWkp_on_precompact_of_locally hul hV hVc hVD
  have hsub : V⊆nativePoissonEntranceCollar := subset_closure.trans hVD
  have hJ := (nativeCollarJetClosure_memH2 J).mono_set (by norm_num : (1:ℝ≥0∞)≤2) hV hsub
  have hK := (nativeCollarJetClosure_memH2 K).mono_set (by norm_num : (1:ℝ≥0∞)≤2) hV hsub
  have hnJ : iteratedWeakSobolevNorm 2 2 J.val.1 V≤13*ENNReal.ofReal ‖J‖ :=
    (wkpNorm_mono_set (by norm_num) hV hsub (nativeCollarJetClosure_memH2 J)).trans (nativeCollarJet_weak_H2_le J)
  have hnK : iteratedWeakSobolevNorm 2 2 K.val.1 V≤13*ENNReal.ofReal ‖K‖ :=
    (wkpNorm_mono_set (by norm_num) hV hsub (nativeCollarJetClosure_memH2 K)).trans (nativeCollarJet_weak_H2_le K)
  have he := weakDivergenceSource_sphere_piecewise_ae hV (subset_refl V) B.a huV hJ hK
    (Filter.EventuallyEq.refl _ _)
  let Z := ENNReal.ofReal ‖J‖+ENNReal.ofReal ‖K‖
  have hu0 : iteratedWeakSobolevNorm 0 2 u V≤13*Z := by
    rw [wkpNorm_zero]
    exact (physicalSplitSource_eLpNorm_le (volume.restrict V) isOpen_ball.measurableSet hJ.memLp hK.memLp).trans
      ((add_le_add ((eLpNorm_le_wkpNorm 2 2 J.val.1 V).trans hnJ)
        ((eLpNorm_le_wkpNorm 2 2 K.val.1 V).trans hnK)).trans_eq (by dsimp [Z];rw [mul_add]))
  have hsource : iteratedWeakSobolevNorm 0 2 (weakDivergenceSource V B.a u) V≤M*(13*Z) := by
    rw [wkpNorm_zero,eLpNorm_congr_ae he]
    calc
      _ ≤ eLpNorm (weakDivergenceSource V B.a J.val.1) 2 (volume.restrict V)+
          eLpNorm (weakDivergenceSource V B.a K.val.1) 2 (volume.restrict V) :=
        physicalSplitSource_eLpNorm_le _ isOpen_ball.measurableSet (hm J.val.1 hJ).1.memLp (hm K.val.1 hK).1.memLp
      _ ≤ M*iteratedWeakSobolevNorm 2 2 J.val.1 V+M*iteratedWeakSobolevNorm 2 2 K.val.1 V := by
        simpa only [wkpNorm_zero] using add_le_add (hm J.val.1 hJ).2 (hm K.val.1 hK).2
      _ ≤ M*(13*ENNReal.ofReal ‖J‖)+M*(13*ENNReal.ofReal ‖K‖) :=
        add_le_add (mul_le_mul le_rfl hnJ zero_le zero_le) (mul_le_mul le_rfl hnK zero_le zero_le)
      _ = _ := by dsimp [Z];ring
  refine ⟨memWkp_on_precompact_of_locally hul hW hWc hWD,?_⟩
  exact (hb u hVD hul).trans ((mul_le_mul le_rfl (add_le_add hu0 hsource) zero_le zero_le).trans_eq
    (by dsimp [Z];ring))

#print axioms physicalSplitSource_eLpNorm_le
#print axioms exists_nativeCollarGlued_H2_bound
end Yamabe3.Analysis.SpherePolar
