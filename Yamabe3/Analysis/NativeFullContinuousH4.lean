import Yamabe3.Analysis.NativeFullAllScaleH4
import Yamabe3.Analysis.WeightedH4ValueBound

/-! A single continuous same-solution family, with uniform bounds for the
full weighted H4 rows and for the retained entrance value coordinate.
The extension is a.e.-compatible before choosing continuous representatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E) 1 \ {(0:E)}
local notation "P" => ({(0:E)}ᶜ : Set E)
local notation "X" => (E→ℝ) × (E→ℝ)

theorem exists_uniform_full_continuous_H4_family
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ (G : X →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞) (K : ℝ)
      (F : DelaunayPhaseData κ → HalfEndPhysicalH2SourceGraph → E → ℝ),
      C ≠ ⊤ ∧ 0 ≤ K ∧
      (∀u v:X,u.1 =ᵐ[volume] v.1 → u.2 =ᵐ[volume] v.2 → G u =ᵐ[volume] G v) ∧
      ∀ (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph),
        Continuous (F p f) ∧ ContDiffOn ℝ 2 (F p f) P ∧ F p f 0 = 0 ∧
        (F p f =ᵐ[volume] G (fullModelCompletionPair hκ0 hκ1 p f)) ∧
        (F p f =ᵐ[volume.restrict O]
          fullModelPhysicalField hκ0 hκ1 p f) ∧
        (∀ s : ℝ, -Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s (F p f)) halfEndBasicAnnulus ∧
          iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s (F p f)) halfEndBasicAnnulus ≤ C*ENNReal.ofReal ‖f‖) ∧
        ∀ x ∈ closedBall (0:E) 4, ‖F p f x‖ ≤ K*‖f‖ := by
  obtain ⟨G,C,hC,hGAE,hG,hlocal,hall⟩ := exists_uniform_full_all_scale_H4_extension hκ0 hκ1
  let Z (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph) : X :=
    fullModelCompletionPair hκ0 hκ1 p f
  have hP : IsOpen P := isClosed_singleton.isOpen_compl
  have hreg (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph) : MemWkpLocally 4 (G (Z p f)) P := by
    intro x hx
    obtain ⟨N,hN,hxN,hNP,hNc⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := x)) hP (singleton_subset_iff.mpr hx)
    obtain ⟨D,hD,hb⟩ := hlocal N hN hNc (fun y hy => hNP hy)
    exact ⟨N,hN,hxN (mem_singleton x),subset_closure.trans hNP,(hb p f).1⟩
  have hex (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph) :=
    exists_continuous_weighted_H4_representative (hreg p f)
      (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (hall p f)
  choose F hFc hF2 hF0 hFAE hFb using hex
  obtain ⟨A,hA,ha⟩ := hlocal (cylinderAnnulus (-5) 6) (isOpen_cylinderAnnulus _ _)
    (isCompact_closure_cylinderAnnulus _ _)
    (fun x hx => cylinderShell_ne_zero (closure_cylinderAnnulus_subset_shell (-5) 6 hx))
  obtain ⟨D,hD,hd⟩ := exists_weighted_H4_entrance_value_bound
  let K := D*(C.toReal+A.toReal)
  refine ⟨G,C,K,F,hC,by dsimp only [K]; positivity,hGAE,?_⟩
  intro p f
  have hForig : F p f =ᵐ[volume.restrict O]
      fullModelPhysicalField hκ0 hκ1 p f := by
    filter_upwards [ae_restrict_of_ae (hFAE p f),ae_restrict_mem (isOpen_ball.sdiff isClosed_singleton).measurableSet,
      fullModelCompletionPair_rep hκ0 hκ1 p f] with x hf hx hz
    exact hf.trans ((hG p f hx).trans hz)
  refine ⟨hFc p f,hF2 p f,hF0 p f,hFAE p f,hForig,hFb p f,?_⟩
  have he : F p f =ᵐ[volume.restrict (cylinderAnnulus (-5) 6)] G (Z p f) := ae_restrict_of_ae (hFAE p f)
  have hh : MemWkp 4 2 (F p f) (cylinderAnnulus (-5) 6) :=
    (MemWkp_congr_ae (by norm_num) (isOpen_cylinderAnnulus _ _) he).mpr (ha p f).1
  have hn : iteratedWeakSobolevNorm 4 2 (F p f) (cylinderAnnulus (-5) 6) ≤ A*ENNReal.ofReal ‖f‖ := by
    rw [wkpNorm_congr_ae (k := 4) (by norm_num) (isOpen_cylinderAnnulus _ _) he]
    exact (ha p f).2
  intro x hx
  have hv := hd (F p f) (hFc p f) (hF0 p f) (C*ENNReal.ofReal ‖f‖) (A*ENNReal.ofReal ‖f‖)
    (by finiteness) (by finiteness) (hFb p f) hh hn x hx
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (norm_nonneg f),← add_mul,mul_assoc,K] using hv

#print axioms exists_uniform_full_continuous_H4_family
end Yamabe3.Analysis.UniformElliptic
