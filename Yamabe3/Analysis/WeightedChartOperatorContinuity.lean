import Yamabe3.Analysis.EuclideanChartRestrictedAE
import Yamabe3.Analysis.WeakDivergenceOperatorContinuity

/-! The weighted pullback of the actual weak divergence operator is
bounded H2 to L2, with a constant fixed before both scalar inputs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_weighted_chart_operator_difference_bound
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e.symm e.target)
    {O W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOs : closure O⊆e.source) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (heW : e '' closure O⊆W)
    (a : E → Matrix (Fin d) (Fin d) ℝ) (ha : ∀ i j,ContDiff ℝ ∞ (fun x => a x i j))
    (σ : E → ℝ) (hσ : ContDiffOn ℝ ∞ σ e.source) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧
      (∀ u : E → ℝ,MemWkp 2 2 u W →
        MemWkp 0 2 (fun x => σ x*weakDivergenceSource W a u (e x)) O) ∧
      ∀ u v : E → ℝ,MemWkp 2 2 u W → MemWkp 2 2 v W →
        iteratedWeakSobolevNorm 0 2
          (fun x => σ x*weakDivergenceSource W a u (e x)-σ x*weakDivergenceSource W a v (e x)) O ≤
          C*iteratedWeakSobolevNorm 2 2 (fun x => u x-v x) W := by
  obtain ⟨A,hA,haB⟩ := exists_weakDivergenceSource_bound hW hWc a ha
  obtain ⟨D,hD,hd⟩ := exists_weakDivergenceSource_difference_bound hW hWc a ha
  obtain ⟨P,hP,hp⟩ := exists_euclidean_chart_source_bound 0 e he hei hO hOc hOs hW heW
  obtain ⟨M,hM,hm⟩ := exists_local_sobolev_multiplier_bound 0 hO hOc e.open_source hOs σ hσ
  refine ⟨M*P*D,by finiteness,?_,?_⟩
  · intro u hu
    exact (hm _ (hp _ (haB u hu).1).1).1
  · intro u v hu hv
    have hdmem := MemWkp.sub (by norm_num : (1:ℝ≥0∞)≤2) hW (haB u hu).1 (haB v hv).1
    have hh := (hm _ (hp _ hdmem).1).2
    simp only [mul_sub] at hh
    exact hh.trans ((mul_le_mul le_rfl (hp _ hdmem).2 zero_le zero_le).trans
      (by simpa only [mul_assoc] using mul_le_mul (le_refl (M*P)) (hd u v hu hv) zero_le zero_le))

#print axioms exists_weighted_chart_operator_difference_bound
end Yamabe3.Analysis.UniformElliptic
