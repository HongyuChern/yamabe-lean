import Yamabe3.Analysis.NativeHighPoissonJetEnergy
import Yamabe3.Analysis.DelaunayPotentialTimeJets
import Yamabe3.Analysis.FullBubblePotentialTimeJets

/-! Actual Delaunay and full-bubble instances discharge all coefficient
jet conditions. The retained solution is the previously constructed
Poisson curve; no additional regularity or derivative witness is chosen. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def DelaunayPhaseData.nativeHighPotential {κ : ℝ} (p : DelaunayPhaseData κ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) : NativeHighPotential where
  κ := κ
  κ_nonneg := hκ0
  κ_lt_one := hκ1
  potential := p.potential
  kernel_bound := p.kernel_bound
  nonneg := p.potential_nonneg
  upper := fun t _ => delaunayPhasePotentialBCF_le p.orbit p.smooth.continuous p.bounded p.phase t

theorem NativeHighPotential.coordinate_regular_four
    (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) (hi : 6 ≤ angularEigenvalue i)
    (hV : ContDiff ℝ 2 (fun t => P.potential t))
    (hV1 : ∀ t : ℝ, |deriv (fun s => P.potential s) t| ≤ 30)
    (hV2 : ∀ t : ℝ, |deriv (deriv (fun s => P.potential s)) t| ≤ 30) :
    let z := nativePoissonCoordinate P b i
    ContDiffOn ℝ 4 z (Ioi 0) ∧
      IntegrableOn (fun t => z t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv z t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv (deriv z) t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv (deriv (deriv z)) t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv (deriv (deriv (deriv z))) t^2) (Ioi 0) := by
  have h1 (t : ℝ) (_ht : 0 < t) : deriv (fun s => P.potential s) t^2 ≤ (30:ℝ)^2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 30)).mpr (hV1 t)
    simpa only [sq_abs] using h
  have h2 (t : ℝ) (_ht : 0 < t) : deriv (deriv (fun s => P.potential s)) t^2 ≤ (30:ℝ)^2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 30)).mpr (hV2 t)
    simpa only [sq_abs] using h
  have h := P.coordinate_higher_jet_energy b i hi hV 30 h1 h2
  exact ⟨h.1, (P.curve_coefficient_square_integral b i).1,
    (P.coordinate_first_energy b i hi).1, h.2.1.1, h.2.2.1.1, h.2.2.2.1⟩

theorem delaunay_native_poisson_regular_four {κ : ℝ} (p : DelaunayPhaseData κ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (b : AngularH1) (i : AngularIndex)
    (hi : 6 ≤ angularEigenvalue i) :
    let z := nativePoissonCoordinate (p.nativeHighPotential hκ0 hκ1) b i
    ContDiffOn ℝ 4 z (Ioi 0) ∧
      IntegrableOn (fun t => z t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv z t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv (deriv z) t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv (deriv (deriv z)) t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv (deriv (deriv (deriv z))) t^2) (Ioi 0) := by
  apply (p.nativeHighPotential hκ0 hκ1).coordinate_regular_four b i hi
    (p.potential_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  · intro t
    exact (p.potential_time_jets_bound t).1.trans (by norm_num)
  · intro t
    exact (p.potential_time_jets_bound t).2.trans (by norm_num)

theorem fullBubble_native_poisson_regular_four (τ : ℝ) (b : AngularH1) (i : AngularIndex)
    (hi : 6 ≤ angularEigenvalue i) :
    let z := nativePoissonCoordinate (fullBubbleHighPotential τ) b i
    ContDiffOn ℝ 4 z (Ioi 0) ∧
      IntegrableOn (fun t => z t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv z t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv (deriv z) t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv (deriv (deriv z)) t^2) (Ioi 0) ∧
      IntegrableOn (fun t => deriv (deriv (deriv (deriv z))) t^2) (Ioi 0) := by
  obtain ⟨hV,hb⟩ := fullBubbleHighPotential_time_jets τ
  apply (fullBubbleHighPotential τ).coordinate_regular_four b i hi
    (hV.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  · intro t
    exact (hb t).1.trans (by norm_num)
  · intro t
    exact (hb t).2.trans (by norm_num)

#print axioms NativeHighPotential.coordinate_regular_four
#print axioms delaunay_native_poisson_regular_four
#print axioms fullBubble_native_poisson_regular_four
end Yamabe3.Analysis.Delaunay
