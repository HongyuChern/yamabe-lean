import Yamabe3.Analysis.WeakChartDivergenceLocal

/-! The coordinate equation of the same native weak H2 field. The density
ratio and smooth operator identity are proved from the given metric and
chart, not supplied as assumptions of this geometric specialization. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

def nativeChartDensityRatio (g : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E E) (x : E) : ℝ :=
  g.pullbackVolumeDensity e x/g.pullbackVolumeDensity id (e x)

theorem nativeChartDensityRatio_smoothOn (g : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (nativeChartDensityRatio g e) e.source := by
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp),hei.mdifferentiableOn (by simp)⟩
  have hρ : ContDiffOn ℝ ∞ (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)).1.contDiffWithinAt
  exact hρ.div ((GreenParametrix.native_density_smooth_positive g).1.comp_contDiffOn he.contDiffOn)
    (fun x _ => ne_of_gt ((GreenParametrix.native_density_smooth_positive g).2 (e x)))

theorem native_weak_chart_divergence
    (g : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O W D V : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOs : closure O⊆e.source) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (heW : e '' closure O⊆W) (hWD : closure W⊆D)
    (hV : IsOpen V) (hOV : O⊆V)
    (b : E → Matrix (Fin 3) (Fin 3) ℝ)
    (hb : ∀ i j,ContDiff ℝ ∞ (fun x => b x i j))
    (hbV : EqOn b (divergenceCoefficients g e) V)
    {u : E → ℝ} (hu : MemWkpLocally 2 u D) :
    MemWkp 2 2 (u∘e) O ∧
      weakDivergenceSource O b (u∘e) =ᵐ[volume.restrict O]
        fun x => nativeChartDensityRatio g e x*weakDivergenceSource W (nativeDivergenceMatrix g) u (e x) := by
  apply weak_chart_divergence_of_smooth_identity_local e he hei hO hOc hOs hW hWc heW hWD
    (nativeDivergenceMatrix g) b (contDiff_nativeDivergenceMatrix g) hb
    (nativeChartDensityRatio g e) (nativeChartDensityRatio_smoothOn g e he hei) _ hu
  intro φ hφ _ x hx
  have hgerm : b =ᶠ[𝓝 x] divergenceCoefficients g e := by
    filter_upwards [hV.mem_nhds (hOV hx)] with y hy
    exact hbV hy
  exact (principalSource_eq_of_matrix_germ (φ∘e) hgerm).trans
    (principalSource_chart_density_ratio g e he hei hφ (hOs (subset_closure hx)))

#print axioms nativeChartDensityRatio_smoothOn
#print axioms native_weak_chart_divergence
end Yamabe3.Analysis.UniformElliptic
