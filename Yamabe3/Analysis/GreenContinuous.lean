import Yamabe3.Analysis.GreenLocalH2
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateRepresentative
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Embedding.MorreyHigherOrder
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Embedding.ExponentIteration
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Iterated.Multiply

/-!
# Continuous local representatives for the three-dimensional L2 correction

The dimension-three embedding used here is explicitly factored as
W2,2 → W1,6 → C0 on a smaller ball. No pointwise regularity is placed in the
input of the native weak inverse.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Metric Filter
open scoped Manifold ContDiff InnerProductSpace Topology ENNReal

namespace Yamabe3.Analysis

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem cutoff_two_derivative_bound {η : E3 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) :
    ∃ C : ℝ, ∀ j ≤ 2, ∀ x : E3, ‖iteratedFDeriv ℝ j η x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) 0).exists_bound_of_continuous
    (hη.continuous_iteratedFDeriv (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 0))
  obtain ⟨C₁, hC₁⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) 1).exists_bound_of_continuous
    (hη.continuous_iteratedFDeriv (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
  obtain ⟨C₂, hC₂⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) 2).exists_bound_of_continuous
    (hη.continuous_iteratedFDeriv (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  refine ⟨max C₀ (max C₁ C₂), fun j hj x => ?_⟩
  interval_cases j
  · exact (hC₀ x).trans (le_max_left _ _)
  · exact (hC₁ x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hC₂ x).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- A genuine Euclidean W2,2 function in dimension three has a continuous
representative near every interior point. The representative is produced by
the subcritical Sobolev step and the proved Morrey representative theorem. -/
theorem exists_continuous_rep_of_H2_three
    {O : Set E3} (hO : IsOpen O) {u : E3 → ℝ}
    (hu : MemWkp 2 2 u O) {x : E3} (hx : x ∈ O) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ O ∧
      ∃ U : E3 → ℝ, Continuous U ∧ u =ᵐ[volume.restrict (ball x r)] U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO x hx
  let R : ℝ := ε / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have h2R : 0 < 2 * R := by positivity
  have hballO : ball x (2 * R) ⊆ O := by
    apply (ball_subset_ball ?_).trans hball
    dsimp [R]
    linarith
  have hinner : closedBall x R ⊆ ball x (2 * R) :=
    closedBall_subset_ball (by linarith)
  obtain ⟨η, hη, hηc, -, hηone, hηsupport, -, -, -⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound
      (isCompact_closedBall x R) isOpen_ball hinner
  obtain ⟨C, hC⟩ := cutoff_two_derivative_bound hη hηc
  have huBall : MemWkp 2 2 u (ball x (2 * R)) :=
    MemWkp.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) isOpen_ball hballO hu
  have hv : MemWkp 2 2 (fun y => η y * u y) (ball x (2 * R)) :=
    MemWkp.smul_smooth_bounded 2 (by norm_num) isOpen_ball hη
      (fun j hj y _ => hC j hj y) huBall
  have hvc : HasCompactSupport (fun y => η y * u y) := hηc.mul_right
  have hvs : tsupport (fun y => η y * u y) ⊆ ball x (2 * R) :=
    tsupport_mul_subset_left.trans hηsupport
  obtain ⟨h6, -⟩ :=
    Poincare.Analysis.Sobolev.EuclideanEmbedding.TowerStep.MemWkp_succ_subcritical_step
      (d := 3) (k := 1) (p := 2) (by norm_num) (by norm_num) isOpen_ball
      hvc hvs (by simpa using hv)
  have h6' : MemWkp 1 (ENNReal.ofReal 6) (fun y => η y * u y) (ball x (2 * R)) := by
    norm_num at h6 ⊢
    exact h6
  obtain ⟨U, hU, hUae⟩ :=
    Poincare.Analysis.Sobolev.EuclideanMorrey.morrey_iteratedFDeriv_representative
      (d := 3) (p := 6) (by norm_num) h2R 0 h6'
  refine ⟨2 * R / 4, by positivity, (ball_subset_ball (by linarith)).trans hballO,
    U, hU.continuous, ?_⟩
  have hηu : u =ᵐ[volume.restrict (ball x (2 * R / 4))] fun y => η y * u y := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hyR : y ∈ closedBall x R := by
      rw [mem_ball] at hy
      rw [mem_closedBall]
      linarith
    rw [hηone y hyR, one_mul]
  exact hηu.trans hUae

section NativeCorrection

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual L2 correction constructed using Yamabe coercivity admits a
continuous coordinate representative at every point, including the proposed
Green pole. This does not construct the singular parametrix itself. -/
theorem closedL2Solution_exists_continuous_coordinate_rep (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (F : Lp ℝ 2 g.volumeMeasure) (x : M) :
    ∃ e : OpenPartialHomeomorph E3 M,
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      ∃ W : Set E3, IsOpen W ∧ W ⊆ e.source ∧ x ∈ e '' W ∧
        ∃ U : E3 → ℝ, Continuous U ∧
          U =ᵐ[volume.restrict W] fun y => toL2 g.leviCivitaData univ
            (closedConformalLaplacianL2Solution g hY F) (e y) := by
  obtain ⟨e, he, hei, O, hO, hOs, hxO, hH2⟩ :=
    closedL2Solution_exists_coordinate_H2 g hY F x
  obtain ⟨y, hy, hyx⟩ := hxO
  obtain ⟨r, hr, hrO, U, hUc, hUae⟩ := exists_continuous_rep_of_H2_three hO hH2 hy
  exact ⟨e, he, hei, ball y r, isOpen_ball, hrO.trans hOs,
    ⟨y, mem_ball_self hr, hyx⟩, U, hUc, hUae.symm⟩

/-- The continuous coordinate representative returns to an actual open
neighborhood in the original manifold, with equality for the native volume.
Thus local continuity is not left as an unconnected Euclidean assertion. -/
theorem closedL2Solution_exists_continuous_native_rep (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (F : Lp ℝ 2 g.volumeMeasure) (x : M) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∃ U : M → ℝ, ContinuousOn U O ∧
        U =ᵐ[g.volumeMeasure.restrict O]
          (toL2 g.leviCivitaData univ (closedConformalLaplacianL2Solution g hY F) : M → ℝ) := by
  obtain ⟨e, he, hei, W, hW, hWs, hxW, U, hUc, hUae⟩ :=
    closedL2Solution_exists_continuous_coordinate_rep g hY F x
  have hWt : e '' W ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hWs hz)
  refine ⟨e '' W, e.isOpen_image_of_subset_source hW hWs, hxW,
    fun y => U (e.symm y), ?_, ?_⟩
  · exact hUc.comp_continuousOn (e.symm.continuousOn.mono hWt)
  · exact g.coordinate_representative_ae e he hei hW hWs hUae

/-- Local continuous representatives glue into one actual continuous
function on the compact original manifold. Native volume positivity gives
pointwise compatibility on overlaps, and compactness supplies a finite
cover for the almost-everywhere conclusion. -/
theorem closedL2Solution_exists_continuous_representative (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (F : Lp ℝ 2 g.volumeMeasure) :
    ∃ U : M → ℝ, Continuous U ∧
      U =ᵐ[g.volumeMeasure]
        (toL2 g.leviCivitaData univ (closedConformalLaplacianL2Solution g hY F) : M → ℝ) := by
  classical
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  choose O hOo hxO U hUc hUae using closedL2Solution_exists_continuous_native_rep g hY F
  have hcompat (i j : M) : EqOn (U i) (U j) (O i ∩ O j) := by
    apply Measure.eqOn_open_of_ae_eq (μ := g.volumeMeasure)
      (EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset inter_subset_left (hUae i))
        (EventuallyEq.symm
          (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hUae j))))
      ((hOo i).inter (hOo j))
      ((hUc i).mono inter_subset_left) ((hUc j).mono inter_subset_right)
  let H : M → ℝ := fun x => U x x
  have hHU (i : M) : EqOn H (U i) (O i) := by
    intro x hx
    exact hcompat x i ⟨hxO x, hx⟩
  have hHc : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have heq : H =ᶠ[𝓝 x] U x :=
      eventuallyEq_iff_exists_mem.mpr ⟨O x, (hOo x).mem_nhds (hxO x), hHU x⟩
    exact ((hUc x).continuousAt ((hOo x).mem_nhds (hxO x))).congr_of_eventuallyEq heq
  have hHae (i : M) : H =ᵐ[g.volumeMeasure.restrict (O i)]
      (toL2 g.leviCivitaData univ (closedConformalLaplacianL2Solution g hY F) : M → ℝ) :=
    EventuallyEq.trans
      ((ae_restrict_iff' (hOo i).measurableSet).mpr (ae_of_all _ (hHU i))) (hUae i)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hOo (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxO x⟩)
  have hall : ∀ᵐ x ∂g.volumeMeasure, ∀ i : s, x ∈ O i.1 → H x =
      toL2 g.leviCivitaData univ (closedConformalLaplacianL2Solution g hY F) x :=
    ae_all_iff.mpr fun i => ae_imp_of_ae_restrict (hHae i.1)
  refine ⟨H, hHc, ?_⟩
  filter_upwards [hall] with x hx
  obtain ⟨i, his, hix⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact hx ⟨i, his⟩ hix

#print axioms exists_continuous_rep_of_H2_three
#print axioms closedL2Solution_exists_continuous_coordinate_rep
#print axioms closedL2Solution_exists_continuous_native_rep
#print axioms closedL2Solution_exists_continuous_representative

end NativeCorrection

end Yamabe3.Analysis
