import Yamabe3.Analysis.BoundaryDifferentiatedSourceBound
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Density

/-! Actual smooth pullback estimates in the full weak Sobolev norm.
The measure domination is an explicit geometric interface. Constants are
chosen before the pulled-back function. Weak inputs are treated separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Every finite weak order on a precompact open set. -/
theorem smooth_memWkp_on_precompact (k : ℕ) {O : Set E}
    (hO : IsOpen O) (hOc : IsCompact (closure O)) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) : MemWkp k 2 f O := by
  obtain ⟨χ, hχ, hc, -, hone, -⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      hOc isOpen_univ (subset_univ _)
  have hh := (MemWkp_of_smooth_compactSupport isOpen_univ (hχ.mul hf) hc.mul_right
    (subset_univ _) (by norm_num : (1 : ℝ≥0∞) ≤ 2) k).mono_set (by norm_num) hO (subset_univ O)
  apply (MemWkp_congr_ae (by norm_num) hO _).mp hh
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  rw [hone x (subset_closure hx), one_mul]

/-- Measure domination gives an actual L2 pullback and its bound. -/
theorem memLp_pullback_of_map_le {O : Set E} {Φ : E → E} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (hmap : (volume.restrict O).map Φ ≤ c • volume)
    (hΦ : AEMeasurable Φ (volume.restrict O)) {f : E → ℝ}
    (hf : MemLp f 2 volume) :
    MemLp (fun x => f (Φ x)) 2 (volume.restrict O) ∧
    eLpNorm (fun x => f (Φ x)) 2 (volume.restrict O) ≤
      c ^ ((1 / (2 : ℝ≥0∞)).toReal) * eLpNorm f 2 volume := by
  have hm := hf.of_measure_le_smul hc hmap
  refine ⟨hm.comp_of_map hΦ, ?_⟩
  have hh := eLpNorm_le_of_measure_le_smul (f := f) (p := (2 : ℝ≥0∞)) hmap
  rw [eLpNorm_map_measure hm.1 hΦ] at hh
  exact hh

/-- Coordinate chain rule with an actual finite expansion. -/
theorem smooth_pullback_partial (Φ : E → E) (hΦ : ContDiff ℝ ∞ Φ)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (x : E) (i : Fin d) :
    fderiv ℝ (fun y => f (Φ y)) x (EuclideanSpace.single i 1) =
      ∑ j : Fin d, (fderiv ℝ Φ x (EuclideanSpace.single i 1)) j *
        fderiv ℝ f (Φ x) (EuclideanSpace.single j 1) := by
  classical
  change fderiv ℝ (f ∘ Φ) x (EuclideanSpace.single i 1) = _
  rw [fderiv_comp x (hf.differentiable (by simp) _) (hΦ.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply]
  have hv (v : E) : v = ∑ j : Fin d, v j • EuclideanSpace.single j 1 := by
    ext l
    simp [PiLp.single_apply, Pi.single_apply]
  calc
    _ = fderiv ℝ f (Φ x) (∑ j : Fin d,
        (fderiv ℝ Φ x (EuclideanSpace.single i 1)) j • EuclideanSpace.single j 1) :=
      congrArg (fderiv ℝ f (Φ x)) (hv _)
    _ = _ := by simp

/-- Fixed smooth maps with dominated coordinate measure give a full Hk
estimate, uniform over smooth compact inputs. -/
theorem exists_smooth_sobolev_pullback_bound
    (k : ℕ) {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (Φ : E → E) (hΦ : ContDiff ℝ ∞ Φ) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hmap : (volume.restrict O).map Φ ≤ c • volume) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      iteratedWeakSobolevNorm k 2 (fun x => f (Φ x)) O ≤
        C * iteratedWeakSobolevNorm k 2 f univ := by
  classical
  let C0 : ℝ≥0∞ := c ^ ((1 / (2 : ℝ≥0∞)).toReal)
  have hC0 : C0 ≠ ⊤ := by simp [C0, hc]
  have hbase (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :=
    (memLp_pullback_of_map_le hc hmap hΦ.continuous.aemeasurable
      (hf.continuous.memLp_of_hasCompactSupport hfc)).2
  induction k with
  | zero =>
    refine ⟨C0, hC0, ?_⟩
    intro f hf hfc
    simpa only [wkpNorm_zero, Measure.restrict_univ] using hbase f hf hfc
  | succ k ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    let a (i j : Fin d) (x : E) : ℝ := (fderiv ℝ Φ x (EuclideanSpace.single i 1)) j
    have ha (i j : Fin d) : ContDiff ℝ ∞ (a i j) :=
      by
        have hh : ContDiff ℝ ∞ (fun x => fderiv ℝ Φ x (EuclideanSpace.single i 1)) :=
          (hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
        exact (PiLp.proj 2 (fun _ : Fin d => ℝ) j).contDiff.comp hh
    choose D hD hbD using fun i j => exists_compact_sobolev_multiplier_bound k hO hOc (a i j) (ha i j)
    refine ⟨C0 + ∑ i, ∑ j, D i j * C, ?_, ?_⟩
    · exact ENNReal.add_ne_top.mpr ⟨hC0, ENNReal.sum_ne_top.mpr fun i _ =>
        ENNReal.sum_ne_top.mpr fun j _ => ENNReal.mul_ne_top (hD i j) hC⟩
    intro f hf hfc
    let df (j : Fin d) (x : E) := fderiv ℝ f x (EuclideanSpace.single j 1)
    have hdf (j : Fin d) : ContDiff ℝ ∞ (df j) :=
      (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdfc (j : Fin d) : HasCompactSupport (df j) := hfc.fderiv_apply ℝ _
    have hfu := MemWkp_of_smooth_compactSupport isOpen_univ hf hfc (subset_univ _)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (k+1)
    have hfo := smooth_memWkp_on_precompact (k+1) hO hOc (hf.comp hΦ)
    have hpart (i : Fin d) :
        iteratedWeakSobolevNorm k 2 (chosenWeakPartial' 2 i (fun x => f (Φ x)) O) O ≤
          (∑ j, D i j * C) * iteratedWeakSobolevNorm (k+1) 2 f univ := by
      have hderiv := chosenWeakPartial_smooth_ae_eq (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        hO (hf.comp hΦ) hfo.memW1p i
      have heq : chosenWeakPartial' 2 i (fun x => f (Φ x)) O =ᵐ[volume.restrict O]
          (fun x => ∑ j, a i j x * df j (Φ x)) := by
        filter_upwards [hderiv] with x hx
        exact hx.trans (smooth_pullback_partial Φ hΦ f hf x i)
      rw [wkpNorm_congr_ae (by norm_num) hO heq]
      have hm (j : Fin d) := smooth_memWkp_on_precompact k hO hOc ((hdf j).comp hΦ)
      calc
        _ ≤ ∑ j, iteratedWeakSobolevNorm k 2 (fun x => a i j x * df j (Φ x)) O :=
          (finite_sobolev_sum_with_bound hO k Finset.univ _
            (fun j _ => memWkp_mul_smooth_of_isCompact_closure k hO hOc (hm j) (ha i j))).2
        _ ≤ ∑ j, D i j * (C * iteratedWeakSobolevNorm (k+1) 2 f univ) := by
          apply Finset.sum_le_sum
          intro j _
          apply (hbD i j _ (hm j)).trans
          apply mul_le_mul le_rfl _ zero_le zero_le
          apply (hbound _ (hdf j) (hdfc j)).trans
          apply mul_le_mul le_rfl _ zero_le zero_le
          rw [← wkpNorm_congr_ae (by norm_num) isOpen_univ
            (chosenWeakPartial_smooth_ae_eq (by norm_num) isOpen_univ hf hfu.memW1p j)]
          exact wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 f univ j
        _ = _ := by simp only [← mul_assoc, Finset.sum_mul]
    rw [wkpNorm_succ_eq]
    calc
      _ ≤ C0 * iteratedWeakSobolevNorm (k+1) 2 f univ +
          ∑ i, (∑ j, D i j * C) * iteratedWeakSobolevNorm (k+1) 2 f univ := by
        apply add_le_add _ (Finset.sum_le_sum fun i _ => hpart i)
        apply (hbase f hf hfc).trans
        apply mul_le_mul le_rfl _ zero_le zero_le
        simpa only [wkpNorm_zero, Measure.restrict_univ] using
          wkpNorm_mono_order (p := (2 : ℝ≥0∞)) (Nat.zero_le (k+1)) f univ
      _ = _ := by rw [add_mul, Finset.sum_mul]

#print axioms smooth_memWkp_on_precompact
#print axioms memLp_pullback_of_map_le
#print axioms smooth_pullback_partial
#print axioms exists_smooth_sobolev_pullback_bound
end Yamabe3.Analysis.UniformElliptic
