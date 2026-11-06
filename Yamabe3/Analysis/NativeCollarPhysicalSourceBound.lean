import Yamabe3.Analysis.NativeCollarJetSobolevBound
import Yamabe3.Analysis.NativeCollarExteriorSourceIdentity
import Yamabe3.Analysis.NativeHalfEndH4Regularity
import Yamabe3.Analysis.SobolevLocalPullback

/-! The genuine inner/outer potentials are smooth off the puncture.
They act boundedly on the retained collar H2 jets on every fixed smaller
domain. The multiplier constant is chosen before the source and field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Yamabe3.Analysis.GreenParametrix Delaunay
open Poincare.Analysis.Sobolev.Euclidean

theorem nativeInnerDivergencePotential_smooth (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) :
    ContDiffOn ℝ ∞ (fun x => annularDelaunayPotential v phase x+nativeDelaunayPotentialError g r v phase x)
      ({0}ᶜ : Set E) := by
  intro x hx
  exact ((contDiffAt_annularDelaunayPotential hv phase hx).add
    (contDiffAt_nativeDelaunayPotentialError g r hv phase hx)).contDiffWithinAt

theorem nativeExteriorDivergencePotential_smooth (g : RiemannianMetric 3 E) (r : ℝ)
    (V : ℝ →ᵇ ℝ) (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t)) :
    ContDiffOn ℝ ∞ (nativeExteriorDivergencePotential g r V) ({0}ᶜ : Set E) := by
  have hs := (contDiff_nativePotentialDensity g).comp (contDiff_id.const_smul r)
  have hρ := (native_density_smooth_positive g).1.comp (contDiff_id.const_smul r)
  exact (contDiffOn_const.mul hs.contDiffOn).sub
    (hρ.contDiffOn.mul (nativeHalfEndPotentialCoefficient_contDiffOn V hVs))

theorem exists_nativeCollar_potential_source_bound {W : Set E}
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWD : closure W⊆nativePoissonEntranceCollar)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set E)) :
    ∃ C : ℝ≥0∞,C≠⊤ ∧ ∀ (J : nativeCollarJetClosure) (f : E → ℝ),
      MemWkp 2 2 f W →
      MemWkp 2 2 (fun x => f x-a x*(J.val.1 : E → ℝ) x) W ∧
      iteratedWeakSobolevNorm 2 2 (fun x => f x-a x*(J.val.1 : E → ℝ) x) W ≤
        iteratedWeakSobolevNorm 2 2 f W+C*ENNReal.ofReal ‖J‖ := by
  have hW0 : closure W⊆({0}ᶜ : Set E) := fun x hx => (hWD hx).1
  obtain ⟨C,hC,hb⟩ := exists_local_sobolev_multiplier_bound 2 hW hWc
    isClosed_singleton.isOpen_compl hW0 a ha
  refine ⟨C*13,by finiteness,?_⟩
  intro J f hf
  have hJ := (nativeCollarJetClosure_memH2 J).mono_set (by norm_num : (1:ℝ≥0∞)≤2)
    hW (subset_closure.trans hWD)
  have hh := hb J.val.1 hJ
  refine ⟨MemWkp.sub (by norm_num) hW hf hh.1,?_⟩
  calc
    _ ≤ iteratedWeakSobolevNorm 2 2 f W+
        iteratedWeakSobolevNorm 2 2 (fun x => a x*(J.val.1 : E → ℝ) x) W :=
      sobolevNorm_sub_le hW hf hh.1
    _ ≤ iteratedWeakSobolevNorm 2 2 f W+C*iteratedWeakSobolevNorm 2 2 J.val.1 W :=
      add_le_add le_rfl hh.2
    _ ≤ iteratedWeakSobolevNorm 2 2 f W+C*(13*ENNReal.ofReal ‖J‖) := by
      apply add_le_add le_rfl
      exact mul_le_mul le_rfl ((wkpNorm_mono_set (by norm_num) hW (subset_closure.trans hWD)
        (nativeCollarJetClosure_memH2 J)).trans (nativeCollarJet_weak_H2_le J)) zero_le zero_le
    _ = _ := by rw [mul_assoc]

#print axioms nativeInnerDivergencePotential_smooth
#print axioms nativeExteriorDivergencePotential_smooth
#print axioms exists_nativeCollar_potential_source_bound
end Yamabe3.Analysis.SpherePolar
