import Yamabe3.Analysis.BoundaryLocalFourthExtension
import Yamabe3.Analysis.SobolevEuclideanChart

/-! Return an actual bounded H4 extension from a boundary chart to the
physical Euclidean neighborhood. It agrees with the same input on the
inside and is defined on both sides. No boundary values of L2 classes
are obtained by restricting a volume-a.e. statement. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.BoundaryTangential
open PoincareMT.LeviCivitaData.Dirichlet
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_chart_physical_linear_extension {Ω : Set E}
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e.symm e.target)
    (hflat : ∀ x ∈ e.source, e x ∈ Ω ↔ 0 < x 0)
    (χ : E → ℝ) {U : Set E} (hU : IsOpen U)
    (hone : ∀ x ∈ U, χ (e x) = 1) (a : E) (ha : a ∈ e.target) (haU : e.symm a ∈ U) :
    ∃ (N : Set E) (L : (E → ℝ) →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞),
      a ∈ N ∧ IsOpen N ∧ IsCompact (closure N) ∧ closure N ⊆ e.target ∧ C ≠ ⊤ ∧
      ∀ u : E → ℝ,
        MemWkp 4 2 (chartPullback e (fun y => χ y*u y))
          (U ∩ halfSpace d) →
        MemWkp 4 2 (L u) N ∧
        iteratedWeakSobolevNorm 4 2 (L u) N ≤ C *
          iteratedWeakSobolevNorm 4 2
            (chartPullback e (fun y => χ y*u y)) (U ∩ halfSpace d) ∧
        EqOn (L u) u (N ∩ Ω) := by
  classical
  obtain ⟨ψ, -, hψU⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 d) (e.symm a)).mem_iff.mp
    (hU.mem_nhds haU)
  obtain ⟨P, hPψ, hP, haP⟩ := mem_nhds_iff.mp ψ.eventuallyEq_one
  have hlim : Tendsto e.symm (𝓝 a) (𝓝 (e.symm a)) := (e.symm.continuousAt ha).tendsto
  have hpre : {y : E | e.symm y ∈ U ∩ P} ∈ 𝓝 a := hlim
    ((hU.inter hP).mem_nhds ⟨haU, haP⟩)
  obtain ⟨T, hTsub, hT, haT⟩ := mem_nhds_iff.mp (inter_mem (e.open_target.mem_nhds ha) hpre)
  obtain ⟨N, hN, haN, hNT, hNc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := a)) hT (singleton_subset_iff.mpr haT)
  have hNt : closure N ⊆ e.target := fun y hy => (hTsub (hNT hy)).1
  let pull (u : E → ℝ) := chartPullback e (fun y => χ y*u y)
  have hpadd (u v : E → ℝ) : pull (u+v) = pull u+pull v := by
    funext x
    by_cases hx : x ∈ e.source <;> simp [pull,chartPullback,hx,mul_add]
  have hpsmul (a : ℝ) (u : E → ℝ) : pull (a • u) = a • pull u := by
    funext x
    by_cases hx : x ∈ e.source <;> simp [pull,chartPullback,hx,mul_left_comm]
  let L : (E → ℝ) →ₗ[ℝ] (E → ℝ) :=
    { toFun := fun u y => localFourthExtension ψ (pull u) (e.symm y)
      map_add' := by
        intro u v
        funext y
        rw [hpadd,localFourthExtension_add]
        rfl
      map_smul' := by
        intro a u
        funext y
        rw [hpsmul,localFourthExtension_smul]
        rfl }
  obtain ⟨C₁, hC₁, h1⟩ := exists_localFourthExtension_bound hU ψ ψ.contMDiff.contDiff ψ.hasCompactSupport hψU
  obtain ⟨C₂, hC₂, h2⟩ := exists_euclidean_chart_source_bound 4 e.symm hei he hN hNc hNt
    isOpen_univ (subset_univ _)
  refine ⟨N, L, C₂*C₁, haN (mem_singleton _), hN, hNc, hNt, by finiteness, ?_⟩
  intro u hu
  have hExt := h1 (pull u) hu
  have hPhys := h2 (localFourthExtension ψ (pull u)) hExt.1
  refine ⟨hPhys.1, hPhys.2.trans ?_, ?_⟩
  · simpa only [mul_assoc] using mul_le_mul (a := C₂) le_rfl hExt.2 zero_le zero_le
  · intro y hy
    have hyt := hNt (subset_closure hy.1)
    have hyUP : e.symm y ∈ U ∩ P := (hTsub (hNT (subset_closure hy.1))).2
    have hyH : e.symm y ∈ halfSpace d := by
      apply (hflat _ (e.map_target hyt)).mp
      simpa only [e.right_inv hyt] using hy.2
    change fourthOrderExtension (fun x => ψ x * pull u x) (e.symm y) = u y
    rw [fourthOrderExtension_eq_on _ hyH, hPψ hyUP.2, Pi.one_apply, one_mul]
    dsimp only [pull]
    rw [chartPullback_apply e _ (e.map_target hyt), hone _ hyUP.1, one_mul, e.right_inv hyt]

#print axioms exists_chart_physical_linear_extension
end Yamabe3.Analysis.UniformElliptic
