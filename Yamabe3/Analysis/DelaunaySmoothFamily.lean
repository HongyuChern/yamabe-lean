import Yamabe3.Analysis.DelaunayNeckNormalization
import PoincareLib.Analysis.ODE.Flow.ParametricComplete
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A genuine jointly smooth neck/time Delaunay family

The phase-plane field is cut off outside a fixed compact set. Its complete
smooth flow is constructed by the pinned ODE theorem. Every previously
constructed Delaunay orbit stays in the region where this actual cutoff is
one. Initial-value uniqueness therefore identifies the flow starting at
(eta,0) with the genuine neck-normalized periodic orbit. Joint smoothness
is derived, not supplied as parameter data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

private abbrev Phase := ℝ × ℝ

private def phaseBump : ContDiffBump (0 : Phase) :=
  ⟨2, 3, by norm_num, by norm_num⟩

private def cutoffPhaseField (x : Phase) : Phase :=
  phaseBump x • (x.2, radialForce x.1)

private theorem cutoffPhaseField_contDiff : ContDiff ℝ ∞ cutoffPhaseField := by
  have hforce : ContDiff ℝ ∞ (fun x : Phase => radialForce x.1) := by
    unfold radialForce
    fun_prop
  exact phaseBump.contDiff.smul (contDiff_snd.prodMk hforce)

private theorem cutoffPhaseField_eq {x : Phase} (hx : ‖x‖ ≤ 2) :
    cutoffPhaseField x = (x.2, radialForce x.1) := by
  have hχ : phaseBump x = 1 := phaseBump.one_of_mem_closedBall (by
    rw [mem_closedBall, dist_zero_right]
    exact hx)
  simp only [cutoffPhaseField, hχ, one_smul]

/-- One actual jointly smooth family, normalized at its neck, contains all
nonconstant positive Delaunay orbits in their natural parameter range.
Outside that range it is merely the constructed compactly cut-off flow. -/
theorem exists_jointly_smooth_delaunay_neck_family :
    ∃ V : ℝ → ℝ → ℝ,
      ContDiff ℝ ∞ (fun z : ℝ × ℝ => V z.1 z.2) ∧
      ∀ η : ℝ, 0 < η → 3 * η ^ 4 < 1 →
        ∃ T : ℝ, 0 < T ∧ Function.Periodic (V η) T ∧
          V η 0 = η ∧ deriv (V η) 0 = 0 ∧
          (∀ t, η ≤ V η t ∧ V η t < 1 ∧ |deriv (V η) t| < V η t / 2) ∧
          (∀ t, deriv (deriv (V η)) t = radialForce (V η t)) ∧
          (∀ t, 4 * deriv (V η) t ^ 2 + V η t ^ 6 - V η t ^ 2 = η ^ 6 - η ^ 2) ∧
          (∀ S, 0 < S → Function.Periodic (V η) S → T ≤ S) := by
  have hfix : ∀ (p : ℝ) (x : Phase), x ∉ tsupport phaseBump → cutoffPhaseField x = 0 := by
    intro _ x hx
    have hz : phaseBump x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [cutoffPhaseField, hz, zero_smul]
  obtain ⟨Φ, hΦ, hiΦ, hdΦ, _, _⟩ :=
    Poincare.ODE.Flow.exists_smooth_parametric_flow
      (H := fun z : ℝ × Phase => cutoffPhaseField z.2)
      (cutoffPhaseField_contDiff.comp contDiff_snd) phaseBump.hasCompactSupport hfix
  let V : ℝ → ℝ → ℝ := fun η t => (Φ 0 t (η, 0)).1
  have hVs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => V z.1 z.2) := by
    have hmap : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ((0 : ℝ), (z.2, (z.1, (0 : ℝ))))) :=
      contDiff_const.prodMk (contDiff_snd.prodMk (contDiff_fst.prodMk contDiff_const))
    exact (hΦ.comp hmap).fst
  refine ⟨V, hVs, ?_⟩
  intro η hη hsmall
  obtain ⟨v, T, hT, hv, hp, hzero, hd0, hb, hode, he, hleast⟩ :=
    exists_delaunay_neck_solution hη hsmall
  have hvd : ContDiff ℝ ∞ (deriv v) := (contDiff_infty_iff_deriv.mp hv).2
  have hstate (t : ℝ) : HasDerivAt (fun y => (v y, deriv v y))
      (cutoffPhaseField (v t, deriv v t)) t := by
    have hvt : 0 < v t := hη.trans_le (hb t).1
    have hn : ‖(v t, deriv v t)‖ ≤ (2 : ℝ) := by
      simp only [Prod.norm_mk, Real.norm_eq_abs]
      apply max_le
      · rw [abs_of_pos hvt]
        linarith [(hb t).2.1]
      · linarith [(hb t).2.1, (hb t).2.2]
    rw [cutoffPhaseField_eq hn]
    have hdv := (hv.differentiable (by simp) t).hasDerivAt
    have hddv := (hvd.differentiable (by simp) t).hasDerivAt
    rw [hode t] at hddv
    exact hdv.prodMk hddv
  have hagree : EqOn (fun t => Φ 0 t (η, 0)) (fun t => (v t, deriv v t)) univ := by
    apply Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ cutoffPhaseField_contDiff.contDiffOn
      isOpen_univ isPreconnected_univ
      (fun t _ => ⟨mem_univ _, hdΦ 0 (η, 0) t⟩)
      (fun t _ => ⟨mem_univ _, hstate t⟩) (mem_univ (0 : ℝ))
    rw [hiΦ]
    simp only [hzero, hd0]
  have heq : V η = v := by
    funext t
    exact congrArg Prod.fst (hagree (mem_univ t))
  refine ⟨T, hT, ?_⟩
  rw [heq]
  exact ⟨hp, hzero, hd0, hb, hode, he, hleast⟩

#print axioms exists_jointly_smooth_delaunay_neck_family

end Yamabe3.Analysis.Delaunay
