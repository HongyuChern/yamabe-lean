import Yamabe3.Analysis.NativeExteriorAllScaleField
import Yamabe3.Analysis.NativeC2CollarEnergyBound

/-! The actual exterior Poisson H2 jet is bounded on all exterior
half-end scales by the same three-halves boundary energy. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem exists_nativeExterior_halfEnd_jet_square_bound (P : NativeHighPotential) :
    ∃D : ℝ,0≤D ∧ ∀(b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b))
      (s : ℝ),s≤0 → ‖nativeExteriorShiftedJet P s b hb‖^2≤
        D*(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_uniform_nativeExteriorPoisson_halfEnd_H2_bounds P
  let D := 1+C+G+∑k : Fin 3,K k
  have hsum : 0≤∑k : Fin 3,K k := Finset.sum_nonneg (fun k _ => hK k)
  have hD : 0≤D := by dsimp [D];linarith
  have hCD : C≤D := by dsimp [D];linarith
  have hGD : G≤D := by dsimp [D];linarith
  have hKD (k : Fin 3) : K k≤D := by
    have hk := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ k)
    dsimp [D];linarith
  refine ⟨D,hD,fun b hb s hs => ?_⟩
  let S := ∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i
  have hS : 0≤S := tsum_nonneg (fun i => sq_nonneg _)
  have hj := h s hs b hb
  have hbnd {x : NativeCollarL2} {E : ℝ} (hED : E≤D) (hx : ‖x‖^2≤E*S) :
      ‖x‖≤Real.sqrt (D*S) :=
    (Real.le_sqrt (norm_nonneg _) (mul_nonneg hD hS)).mpr
      (hx.trans (mul_le_mul_of_nonneg_right hED hS))
  have hn := nativeCollarJet_norm_le_of_components (nativeExteriorShiftedJet P s b hb) (Real.sqrt_nonneg _)
    (hbnd hCD hj.1) (fun j => hbnd hGD (hj.2.1 j)) (fun k j => hbnd (hKD k) (hj.2.2 k j))
  exact ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hn).trans_eq (Real.sq_sqrt (mul_nonneg hD hS))

theorem exists_nativeExterior_halfEnd_family_bound {X : Type*} [NormedAddCommGroup X]
    (P : NativeHighPotential) (b : X→AngularH1)
    (hb : ∀x,NativeAngularSpectralRegular (3/2) (angularEmbedding (b x)))
    (he : ∃D : ℝ,0≤D ∧ ∀x,(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (b x)) i)≤D*‖x‖^2) :
    ∃C : ℝ,0≤C ∧ ∀x s,s≤0 → ‖nativeExteriorShiftedJet P s (b x) (hb x)‖≤C*‖x‖ := by
  obtain ⟨D,hD,hd⟩ := he
  obtain ⟨L,hL,hl⟩ := exists_nativeExterior_halfEnd_jet_square_bound P
  refine ⟨Real.sqrt (L*D),Real.sqrt_nonneg _,fun x s hs => ?_⟩
  have h := (hl (b x) (hb x) s hs).trans (mul_le_mul_of_nonneg_left (hd x) hL)
  have hh : (Real.sqrt (L*D)*‖x‖)^2=L*(D*‖x‖^2) := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hL hD)];ring
  have hn : 0≤Real.sqrt (L*D)*‖x‖ := by positivity
  nlinarith only [h,hh,hn,norm_nonneg (nativeExteriorShiftedJet P s (b x) (hb x))]

#print axioms exists_nativeExterior_halfEnd_jet_square_bound
#print axioms exists_nativeExterior_halfEnd_family_bound
end Yamabe3.Analysis.SpherePolar
