import Yamabe3.Analysis.NativeC2CollarSeriesNorm
import Yamabe3.Analysis.NativeCollarJetSpace

/-! A uniform norm estimate for the genuine physical H2 collar jet in
terms of value and Laplacian energy on the larger collar. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

def nativeC2WindowEnergy (u : E→ℝ) : ℝ :=
  (∫x in nativePolarTimeWindow (Ioo (-1) 1),u x^2)+
  (∫x in nativePolarTimeWindow (Ioo (-1) 1),nativeCoordinateLaplacian u x^2)

theorem nativeC2WindowEnergy_nonneg (u : E→ℝ) : 0≤nativeC2WindowEnergy u :=
  add_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (integral_nonneg (fun _ => sq_nonneg _))

theorem nativeCollarJet_norm_le_of_components (J : nativeCollarJetClosure) {C : ℝ} (hC : 0≤C)
    (h0 : ‖J.val.1‖≤C) (h1 : ∀j,‖J.val.2.1 j‖≤C) (h2 : ∀k j,‖J.val.2.2 k j‖≤C) :
    ‖J‖≤C := by
  change ‖J.val‖≤C
  rw [Prod.norm_def,max_le_iff,Prod.norm_def,max_le_iff]
  exact ⟨h0,(pi_norm_le_iff_of_nonneg hC).mpr h1,
    (pi_norm_le_iff_of_nonneg hC).mpr (fun k => (pi_norm_le_iff_of_nonneg hC).mpr (h2 k))⟩

theorem exists_nativeC2Collar_energy_bound :
    ∃C : ℝ,0≤C ∧ ∀u : nativeC2OffZero,
      ‖nativeC2CollarJetInclusion u‖^2≤C*nativeC2WindowEnergy u.val := by
  obtain ⟨G,K,hG,hK,h⟩ := exists_nativeC2Collar_series_norm_bounds (ι := Unit)
  let C := 1+G+∑k : Fin 3,K k
  have hsum : 0≤∑k : Fin 3,K k := Finset.sum_nonneg (fun k _ => hK k)
  have hC : 0≤C := by dsimp [C]; linarith
  have h1C : 1≤C := by dsimp [C]; linarith
  have hGC : G≤C := by dsimp [C]; linarith
  have hKC (k : Fin 3) : K k≤C := by
    have hk := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ k)
    dsimp [C]; linarith
  refine ⟨C,hC,fun u => ?_⟩
  have he := nativeC2WindowEnergy_nonneg u.val
  have hbudget (s : Finset Unit) :
      (∫x in nativePolarTimeWindow (Ioo (-1) 1),(∑i∈s,u.val x)^2)+
        (∫x in nativePolarTimeWindow (Ioo (-1) 1),nativeCoordinateLaplacian (fun y => ∑i∈s,u.val y) x^2)≤
      (1:ℝ)*(∑i∈s,nativeC2WindowEnergy u.val) := by
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst s
      simp [nativeCoordinateLaplacian,nativeCoordinateSecond,nativeCoordinateFirst]
    · have hs' : s=Finset.univ := by
        apply Finset.ext
        intro i
        simp only [Finset.mem_univ,iff_true]
        obtain ⟨j,hj⟩ := hs
        exact (Subsingleton.elim j i) ▸ hj
      subst s
      simp [nativeC2WindowEnergy]
  have hb := h (fun _ : Unit => u.val) (fun _ => u.property)
    (fun _ => nativeC2WindowEnergy u.val) (hasSum_fintype _).summable (fun _ => he) 1 (by norm_num) hbudget
  simp only [tsum_fintype,Finset.univ_unique,Finset.sum_singleton,mul_one,one_mul] at hb
  have hbound {x : NativeCollarL2} {D : ℝ} (hDC : D≤C) (hx : ‖x‖^2≤D*nativeC2WindowEnergy u.val) :
      ‖x‖≤Real.sqrt (C*nativeC2WindowEnergy u.val) := by
    have hh := hx.trans (mul_le_mul_of_nonneg_right hDC he)
    exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg hC he)).mpr hh
  have hn := nativeCollarJet_norm_le_of_components (nativeC2CollarJetInclusion u) (Real.sqrt_nonneg _)
    (by change ‖nativeC2CollarValue u.property‖≤_; exact hbound h1C (by simpa only [one_mul] using hb.1))
    (fun j => by change ‖nativeC2CollarFirst u.property j‖≤_; exact hbound hGC (hb.2.1 j))
    (fun k j => by change ‖nativeC2CollarSecond u.property k j‖≤_; exact hbound (hKC k) (hb.2.2 k j))
  exact ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hn).trans_eq (Real.sq_sqrt (mul_nonneg hC he))

#print axioms nativeC2WindowEnergy_nonneg
#print axioms nativeCollarJet_norm_le_of_components
#print axioms exists_nativeC2Collar_energy_bound
end Yamabe3.Analysis.SpherePolar
