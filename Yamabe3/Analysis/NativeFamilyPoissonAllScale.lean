import Yamabe3.Analysis.NativeFamilyTailBounds

/-! Constants chosen before the potential, for the original solver and
entrance correction. No new field or boundary condition is substituted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

private theorem combine_square_bound {n a d E S N : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hN : 0 ≤ N) (hS : 0 ≤ S)
    (hE : E=N+S) (hn : 0 ≤ n) :
    (n^2 ≤ a*S ∨ n ≤ d*Real.sqrt N) → n^2 ≤ (a+d^2)*E := by
  intro h
  rcases h with h | h
  · rw [hE]
    nlinarith [mul_nonneg ha hN,mul_nonneg (sq_nonneg d) hN,mul_nonneg (sq_nonneg d) hS]
  · have hb := sq_le_sq₀ hn (mul_nonneg hd (Real.sqrt_nonneg N)) |>.2 h
    rw [mul_pow,Real.sq_sqrt hN] at hb
    rw [hE]
    nlinarith [mul_nonneg ha hN,mul_nonneg ha hS,mul_nonneg (sq_nonneg d) hS]

 theorem exists_family_nativePoissonAllScale_H2_bounds {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0 ≤ C ∧ 0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ),
      ∀ (b : AngularH1),NativeAngularSpectralRegular (3/2) (angularEmbedding b) → ∀ s : ℝ,
        ‖nativePoissonAllScaleValue P hplus s b‖^2 ≤ C*nativePoissonBoundaryEnergy b ∧
        (∀ j,‖nativePoissonAllScaleFirst P hplus s b j‖^2 ≤ G*nativePoissonBoundaryEnergy b) ∧
        (∀ k j,‖nativePoissonAllScaleSecond P hplus s b k j‖^2 ≤ K k*nativePoissonBoundaryEnergy b) := by
  obtain ⟨C,G,K,hC,hG,hK,he⟩ := exists_family_nativeShiftedEntrance_H2_bounds hκ0 hκ1 hM
  obtain ⟨D,H,L,hD,hH,hL,ht⟩ := exists_family_nativePoissonTail_H2_bounds hκ0 hκ1 hM
  refine ⟨C+D^2,G+H^2,fun k => K k+(L k)^2,by positivity,by positivity,
    fun k => add_nonneg (hK k) (sq_nonneg _),?_⟩
  intro P hP hPM hplus b hb s
  have he := he P hP hPM
  have ht := ht P hP hPM hplus
  have hE : nativePoissonBoundaryEnergy b=‖b‖^2+(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := rfl
  have hS : 0 ≤ (∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := tsum_nonneg (fun i => sq_nonneg _)
  have hsqrt : Real.sqrt (‖b‖^2)=‖b‖ := Real.sqrt_sq (norm_nonneg _)
  by_cases hs : s ≤ 2
  · have h := he s hs b hb
    simp only [nativePoissonAllScaleValue,nativePoissonAllScaleFirst,nativePoissonAllScaleSecond,if_pos hs]
    exact ⟨combine_square_bound hC hD (sq_nonneg _) hS hE (norm_nonneg _) (Or.inl h.1),
      fun j => combine_square_bound hG hH (sq_nonneg _) hS hE (norm_nonneg _) (Or.inl (h.2.1 j)),
      fun k j => combine_square_bound (hK k) (hL k) (sq_nonneg _) hS hE (norm_nonneg _) (Or.inl (h.2.2 k j))⟩
  · have h := ht s (by linarith) b
    simp only [nativePoissonAllScaleValue,nativePoissonAllScaleFirst,nativePoissonAllScaleSecond,if_neg hs]
    exact ⟨combine_square_bound hC hD (sq_nonneg _) hS hE (norm_nonneg _) (Or.inr (hsqrt.symm ▸ h.1)),
      fun j => combine_square_bound hG hH (sq_nonneg _) hS hE (norm_nonneg _) (Or.inr (hsqrt.symm ▸ h.2.1 j)),
      fun k j => combine_square_bound (hK k) (hL k) (sq_nonneg _) hS hE (norm_nonneg _) (Or.inr (hsqrt.symm ▸ h.2.2 k j))⟩

#print axioms exists_family_nativePoissonAllScale_H2_bounds
end Yamabe3.Analysis.SpherePolar
