import Yamabe3.Analysis.NativeC2CollarSeriesNorm

/-! The previously proved local elliptic estimates, specialized to one
actual C2 field. The constants depend only on the fixed nested collars. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

theorem exists_nativeC2Collar_single_energy_bounds :
    ∃ (G : ℝ) (K : Fin 3 → ℝ),0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (u : E → ℝ) (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) (C : ℝ),0 ≤ C →
      ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),u x^2)+
        (∫ x in nativePolarTimeWindow (Ioo (-1) 1),nativeCoordinateLaplacian u x^2)) ≤ C →
      ‖nativeC2CollarValue hu‖^2 ≤ C ∧
      (∀ j,‖nativeC2CollarFirst hu j‖^2 ≤ G*C) ∧
      (∀ k j,‖nativeC2CollarSecond hu k j‖^2 ≤ K k*C) := by
  obtain ⟨G,K,hG,hK,h⟩ := exists_nativeC2Collar_series_norm_bounds (ι := Unit)
  refine ⟨G,K,hG,hK,fun u hu C hC he => ?_⟩
  have hb (s : Finset Unit) :
      ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),(∑ _i ∈ s,u x)^2)+
        (∫ x in nativePolarTimeWindow (Ioo (-1) 1),nativeCoordinateLaplacian (fun y => ∑ _i ∈ s,u y) x^2)) ≤
          C*(∑ _i ∈ s,(1:ℝ)) := by
    by_cases hs : ()∈s
    · have heq : s=Finset.univ := by ext x; cases x; simpa using hs
      simpa only [heq,Fintype.sum_unique,mul_one] using he
    · have heq : s=∅ := by ext x; cases x; simpa using hs
      simp [heq,nativeCoordinateLaplacian]
  have hh := h (fun _ : Unit => u) (fun _ => hu) (fun _ => (1:ℝ)) (Summable.of_finite)
    (fun _ => by norm_num) C hC hb
  simpa only [tsum_fintype,Fintype.sum_unique,mul_one] using hh

#print axioms exists_nativeC2Collar_single_energy_bounds
end Yamabe3.Analysis.SpherePolar
