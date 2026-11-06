import Yamabe3.Analysis.DelaunayCompactParameterJets
import Yamabe3.Analysis.BoundaryChartUniformPotential

/-! Uniform density-weighted chart potential jets from the actual bounded
Delaunay state flow, on the fixed entrance chart. The constant precedes
the orbit and phase. No family-uniform derivative bound is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter Metric PoincareMT
open scoped ContDiff Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_delaunay_chart_potential_jets
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hzero : ∀ x ∈ e.target, x ≠ 0)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v →
      (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀ t, deriv (deriv v) t = radialForce (v t)) →
      ∀ (τ : ℝ) (n : ℕ), n ≤ k → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n (fun y =>
          (RiemannianMetric.euclideanMetric 3).pullbackVolumeDensity e y *
            (-annularDelaunayPotential v τ (e y))) x‖ ≤ C := by
  obtain ⟨Φ,hΦ,-,-,horbit⟩ := exists_delaunay_state_flow
  let ρ := (RiemannianMetric.euclideanMetric 3).pullbackVolumeDensity e
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp),hei.mdifferentiableOn (by simp)⟩
  have hρ (x : E) (hx : x ∈ e.source) : ContDiffAt ℝ ∞ ρ x :=
    ((RiemannianMetric.euclideanMetric 3).contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)).1
  let F : DelaunayState × E → ℝ := fun q =>
    ρ q.2 * ((15/4:ℝ) * (Φ (-Real.log ‖e q.2‖) q.1).1^4 / ‖e q.2‖^2)
  have hF : ∀ q : DelaunayState × E, q.2 ∈ e.source → ContDiffAt ℝ ∞ F q := by
    intro q hq
    have heq : ContDiffAt ℝ ∞ e q.2 := he.contDiffOn.contDiffAt (e.open_source.mem_nhds hq)
    have hex := heq.comp q contDiffAt_snd
    have hn : ContDiffAt ℝ ∞ (fun p : DelaunayState × E => ‖e p.2‖) q :=
      (contDiffAt_norm ℝ (hzero _ (e.map_source hq))).comp q hex
    have hl := ((Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr (hzero _ (e.map_source hq)))).comp q hn).neg
    have hp := hΦ.contDiffAt.comp q (hl.prodMk contDiffAt_fst)
    exact ((hρ q.2 hq).comp q contDiffAt_snd).mul
      ((contDiffAt_const.mul (hp.fst.pow 4)).div (hn.pow 2)
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hzero _ (e.map_source hq)))))
  obtain ⟨C,hC,hb⟩ := exists_state_compact_spatial_jet_bound hK hKs hF k
  refine ⟨C,hC,?_⟩
  intro v hv hvb hODE τ n hn x hx
  have hs : ‖(v τ,deriv v τ)‖ ≤ (2:ℝ) := by
    simp only [Prod.norm_mk, Real.norm_eq_abs]
    apply max_le
    · rw [abs_of_nonneg (hvb τ).1]
      linarith [(hvb τ).2.1]
    · linarith [(hvb τ).2.2]
  have heq : (fun y => ρ y * (-annularDelaunayPotential v τ (e y))) =
      fun y => F ((v τ,deriv v τ),y) := by
    funext y
    dsimp only [F,annularDelaunayPotential]
    rw [horbit v hv hvb hODE τ (-Real.log ‖e y‖)]
    simp only [sub_eq_add_neg]
    ring
  change ‖iteratedFDeriv ℝ n (fun y => ρ y * (-annularDelaunayPotential v τ (e y))) x‖ ≤ C
  rw [heq]
  exact hb _ hs n hn x hx

#print axioms exists_uniform_delaunay_chart_potential_jets
end Yamabe3.Analysis.UniformElliptic
