import Yamabe3.Analysis.NativeBubbleLowCollarEquation
import Yamabe3.Analysis.FullBubblePotentialTimeJets
import Yamabe3.Analysis.FiniteSmoothSobolevFamily
import Yamabe3.Analysis.Cylinder.PhysicalTransposedH1

/-! The actual finite low-mode compensation is smooth off the puncture
and has a Sobolev bound uniform in its coefficients on a fixed collar.
The physical forcing normalization and its sign are unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal Manifold
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic SphereSpectrum Delaunay
open Poincare.Analysis.Sobolev.Euclidean

def nativeBubbleCompensationBasis (τ : ℝ) (i : AngularIndex) : E → ℝ :=
  physicalForcing (separableCylinder (fun t => -bubbleCompensation i (τ+t)) (angularRepresentative i))

theorem nativeBubbleCompensationBasis_smooth (τ : ℝ) (i : AngularIndex) :
    ContDiffOn ℝ ∞ (nativeBubbleCompensationBasis τ i) ({0}ᶜ : Set E) :=
  contDiffOn_physicalForcing (smooth_separableCylinder
    (((bubbleCompensation_smooth_compact i).1.comp (contDiff_const.add contDiff_id)).neg)
    (smooth_angularRepresentative i))

theorem nativeBubbleCollarCompensation_eq_sum (τ : ℝ) (c : AngularIndex → ℝ) :
    nativeBubbleCollarCompensation τ c=fun x => ∑i∈nativeLowIndexFinset,c i*nativeBubbleCompensationBasis τ i x := by
  funext x
  by_cases hx : x=0
  · subst x
    simp [nativeBubbleCollarCompensation,nativeBubbleCompensationBasis,physicalForcing]
  · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
    change nativeBubbleCollarCompensation τ c (y:E)=∑i∈nativeLowIndexFinset,c i*nativeBubbleCompensationBasis τ i (y:E)
    simp only [nativeBubbleCollarCompensation,nativeBubbleCompensationBasis,physicalForcing,cylinderLift_coe,
      puncturedCylinderLift,finiteAngular,separableCylinder]
    simp_rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem nativeBubbleCollarCompensation_smooth (τ : ℝ) (c : AngularIndex → ℝ) :
    ContDiffOn ℝ ∞ (nativeBubbleCollarCompensation τ c) ({0}ᶜ : Set E) :=
  contDiffOn_physicalForcing (smooth_finiteAngular nativeLowIndexFinset _
    (fun i _ => contDiff_const.mul ((bubbleCompensation_smooth_compact i).1.comp (contDiff_const.add contDiff_id))))

theorem exists_nativeBubbleCompensation_sobolev_bound (τ : ℝ) (k : ℕ)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O)) (hO0 : closure O⊆({0}ᶜ : Set E)) :
    ∃C : ℝ≥0∞,C≠⊤ ∧ ∀(c : AngularIndex → ℝ) (B : ℝ),
      (∀i∈nativeLowIndexFinset,‖c i‖≤B) →
      MemWkp k 2 (nativeBubbleCollarCompensation τ c) O ∧
      iteratedWeakSobolevNorm k 2 (nativeBubbleCollarCompensation τ c) O≤C*ENNReal.ofReal B := by
  obtain ⟨C,hC,hb⟩ := exists_finite_smooth_sobolev_bound nativeLowIndexFinset
    (nativeBubbleCompensationBasis τ) k hO hOc isClosed_singleton.isOpen_compl hO0
    (fun i _ => nativeBubbleCompensationBasis_smooth τ i)
  refine ⟨C,hC,?_⟩
  intro c B hB
  simpa only [nativeBubbleCollarCompensation_eq_sum] using hb c B hB

theorem nativeBubbleExteriorPotential_smooth (τ : ℝ) :
    ContDiff ℝ ∞ (fun t => nativePoissonExteriorPotential (fullBubbleHighPotential (-τ)) t) :=
  (fullBubbleHighPotential_time_jets (-τ)).1.comp contDiff_neg

#print axioms nativeBubbleCompensationBasis_smooth
#print axioms nativeBubbleCollarCompensation_eq_sum
#print axioms nativeBubbleCollarCompensation_smooth
#print axioms exists_nativeBubbleCompensation_sobolev_bound
#print axioms nativeBubbleExteriorPotential_smooth
end Yamabe3.Analysis.SpherePolar
