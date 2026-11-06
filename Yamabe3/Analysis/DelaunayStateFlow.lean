import Yamabe3.Analysis.DelaunaySmoothFamily

/-!
# One genuine smooth phase flow for all bounded Delaunay orbits

The fixed compact cutoff is identically one on the actual phase box.
Uniqueness identifies every time translate of every bounded actual orbit
with the same complete smooth flow. Compact phase sets can consequently
give constants independent of the neck and of the time translate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology

namespace Yamabe3.Analysis.Delaunay

abbrev DelaunayState := ℝ × ℝ

def orbitPhaseBump : ContDiffBump (0 : DelaunayState) :=
  ⟨2, 3, by norm_num, by norm_num⟩

def orbitPhaseField (x : DelaunayState) : DelaunayState :=
  orbitPhaseBump x • (x.2, radialForce x.1)

theorem orbitPhaseField_contDiff : ContDiff ℝ ∞ orbitPhaseField := by
  have hforce : ContDiff ℝ ∞ (fun x : DelaunayState => radialForce x.1) := by
    unfold radialForce
    fun_prop
  exact orbitPhaseBump.contDiff.smul (contDiff_snd.prodMk hforce)

theorem orbitPhaseField_eq {x : DelaunayState} (hx : ‖x‖ ≤ 2) :
    orbitPhaseField x = (x.2, radialForce x.1) := by
  have hχ : orbitPhaseBump x = 1 := orbitPhaseBump.one_of_mem_closedBall (by
    simpa only [mem_closedBall, dist_zero_right, orbitPhaseBump] using hx)
  simp only [orbitPhaseField, hχ, one_smul]

theorem exists_delaunay_state_flow :
    ∃ Φ : ℝ → DelaunayState → DelaunayState,
      ContDiff ℝ ∞ (fun z : ℝ × DelaunayState => Φ z.1 z.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ x t, HasDerivAt (fun s => Φ s x) (orbitPhaseField (Φ t x)) t) ∧
      ∀ (v : ℝ → ℝ), ContDiff ℝ ∞ v →
        (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1 / 2) →
        (∀ t, deriv (deriv v) t = radialForce (v t)) →
        ∀ τ s, Φ s (v τ, deriv v τ) = (v (τ + s), deriv v (τ + s)) := by
  have hfix : ∀ (p : ℝ) (x : DelaunayState),
      x ∉ tsupport orbitPhaseBump → orbitPhaseField x = 0 := by
    intro _ x hx
    have hz : orbitPhaseBump x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [orbitPhaseField, hz, zero_smul]
  obtain ⟨Ψ, hΨ, hiΨ, hdΨ, _, _⟩ :=
    Poincare.ODE.Flow.exists_smooth_parametric_flow
      (H := fun z : ℝ × DelaunayState => orbitPhaseField z.2)
      (orbitPhaseField_contDiff.comp contDiff_snd) orbitPhaseBump.hasCompactSupport hfix
  let Φ : ℝ → DelaunayState → DelaunayState := Ψ 0
  have hΦ : ContDiff ℝ ∞ (fun z : ℝ × DelaunayState => Φ z.1 z.2) :=
    hΨ.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨Φ, hΦ, hiΨ 0, hdΨ 0, ?_⟩
  intro v hv hb hODE τ s
  have hvd : ContDiff ℝ ∞ (deriv v) := (contDiff_infty_iff_deriv.mp hv).2
  have hstate (t : ℝ) : HasDerivAt (fun r => (v (τ + r), deriv v (τ + r)))
      (orbitPhaseField (v (τ + t), deriv v (τ + t))) t := by
    have hn : ‖(v (τ + t), deriv v (τ + t))‖ ≤ (2 : ℝ) := by
      simp only [Prod.norm_mk, Real.norm_eq_abs]
      apply max_le
      · rw [abs_of_nonneg (hb _).1]
        linarith [(hb (τ + t)).2.1]
      · linarith [(hb (τ + t)).2.2]
    rw [orbitPhaseField_eq hn]
    have hdv := ((hv.differentiable (by simp) (τ + t)).hasDerivAt).comp t
      ((hasDerivAt_id t).const_add τ)
    have hddv := ((hvd.differentiable (by simp) (τ + t)).hasDerivAt).comp t
      ((hasDerivAt_id t).const_add τ)
    simp only [Function.comp_def, mul_one] at hdv hddv
    rw [hODE] at hddv
    exact hdv.prodMk hddv
  apply Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ orbitPhaseField_contDiff.contDiffOn
    isOpen_univ isPreconnected_univ
    (fun t _ => ⟨mem_univ _, hdΨ 0 (v τ, deriv v τ) t⟩)
    (fun t _ => ⟨mem_univ _, hstate t⟩) (mem_univ (0 : ℝ)) ?_ (mem_univ s)
  simp only [hiΨ, add_zero]

#print axioms exists_delaunay_state_flow

end Yamabe3.Analysis.Delaunay
