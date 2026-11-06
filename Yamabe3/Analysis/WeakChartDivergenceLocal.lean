import Yamabe3.Analysis.WeakChartDivergenceLimit
import Yamabe3.Analysis.SobolevLocalCompactExtension

/-! Local H2, rather than a global compact input, suffices for the actual
coordinate identity. The compact extension agrees on a neighborhood of the
whole retained physical region; all resulting weak derivatives are identified. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem weak_chart_divergence_of_smooth_identity_local
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O W D : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOs : closure O⊆e.source) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (heW : e '' closure O⊆W) (hWD : closure W⊆D)
    (a b : E → Matrix (Fin 3) (Fin 3) ℝ)
    (ha : ∀ i j,ContDiff ℝ ∞ (fun x => a x i j))
    (hb : ∀ i j,ContDiff ℝ ∞ (fun x => b x i j))
    (σ : E → ℝ) (hσ : ContDiffOn ℝ ∞ σ e.source)
    (hsmooth : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ x∈O,principalSource b (φ∘e) x=σ x*principalSource a φ (e x))
    {u : E → ℝ} (hu : MemWkpLocally 2 u D) :
    MemWkp 2 2 (u∘e) O ∧
      weakDivergenceSource O b (u∘e) =ᵐ[volume.restrict O]
        fun x => σ x*weakDivergenceSource W a u (e x) := by
  obtain ⟨v,U,hU,hWU,hvc,hv,hvu⟩ := exists_compact_sobolev_extension_near_compact hu hWc hWD
  have hvuW : v =ᵐ[volume.restrict W] u := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
    exact hvu (hWU (subset_closure hx))
  have hmaps : MapsTo e O W := fun x hx => heW (mem_image_of_mem e (subset_closure hx))
  have hvuO := euclidean_chart_comp_congr_ae_restrict e he hei hO hW
    (subset_closure.trans hOs) hmaps hvuW
  have ht := weak_chart_divergence_of_smooth_identity_compact e he hei hO hOc hOs hW hWc heW
    a b ha hb σ hσ hsmooth hv hvc
  have hsrc := euclidean_chart_comp_congr_ae_restrict e he hei hO hW
    (subset_closure.trans hOs) hmaps (weakDivergenceSource_congr_ae hW a hvuW)
  refine ⟨(MemWkp_congr_ae (by norm_num) hO hvuO).mp ht.1,?_⟩
  exact (weakDivergenceSource_congr_ae hO b hvuO).symm.trans (ht.2.trans
    (hsrc.mono (fun x hx => congrArg (σ x*·) hx)))

#print axioms weak_chart_divergence_of_smooth_identity_local
end Yamabe3.Analysis.UniformElliptic
