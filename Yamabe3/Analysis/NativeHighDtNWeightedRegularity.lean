import Yamabe3.Analysis.NativeHighPoissonEnergy
import Yamabe3.Analysis.NativeHighCoupledWeightedRegularity

/-! The true DtN loses one spectral derivative, with its actual bound.
The same coupled Cauchy witness consequently works on each spectral
trace scale; no new independent boundary inverse is postulated. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem NativeHighPotential.derivativeBound_nonneg (P : NativeHighPotential) :
    0 ≤ P.derivativeBound := by
  unfold NativeHighPotential.derivativeBound
  have h := P.κ_lt_one
  positivity

theorem NativeHighPotential.dtn_weighted_square
    (P : NativeHighPotential) (b : AngularH1) (s : ℝ) (i : AngularIndex) :
    nativeAngularWeightedSquare s (P.dtn b) i ≤
      P.derivativeBound^2*nativeAngularWeightedSquare (s+1) (angularEmbedding b) i := by
  unfold nativeAngularWeightedSquare
  rw [P.coefficient]
  split_ifs with hi
  · have hl := P.symbol_lower i hi
    have hu := P.symbol_upper i
    have hw := angularEnergyWeight_pos i
    have hs : 0 ≤ P.symbol i := by linarith
    have hsq : P.symbol i^2 ≤ (P.derivativeBound*angularEnergyWeight i)^2 :=
      (sq_le_sq₀ hs (mul_nonneg P.derivativeBound_nonneg hw.le)).mpr hu
    have h := mul_le_mul_of_nonneg_right hsq
      (sq_nonneg ((angularEnergyWeight i)^s*inner ℝ (angularBasis i) (angularEmbedding b)))
    rw [Real.rpow_add hw, Real.rpow_one]
    nlinarith only [h]
  · simp only [mul_zero, zero_pow (by decide : 2≠0)]
    positivity

theorem NativeHighPotential.dtn_spectral_regular
    (P : NativeHighPotential) (b : AngularH1) (s : ℝ)
    (hb : NativeAngularSpectralRegular (s+1) (angularEmbedding b)) :
    NativeAngularSpectralRegular s (P.dtn b) ∧
      (∑' i, nativeAngularWeightedSquare s (P.dtn b) i) ≤
        P.derivativeBound^2*(∑' i, nativeAngularWeightedSquare (s+1) (angularEmbedding b) i) := by
  have hmaj := hb.mul_left (P.derivativeBound^2)
  have hs : NativeAngularSpectralRegular s (P.dtn b) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (P.dtn_weighted_square b s) hmaj
  refine ⟨hs, ?_⟩
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (P.dtn_weighted_square b s) hs hmaj

theorem nativeAngularSpectralRegular_sub {s : ℝ} {f g : AngularL2}
    (hf : NativeAngularSpectralRegular s f) (hg : NativeAngularSpectralRegular s g) :
    NativeAngularSpectralRegular s (f-g) ∧
      (∑' i, nativeAngularWeightedSquare s (f-g) i) ≤
        2*((∑' i, nativeAngularWeightedSquare s f i)+(∑' i, nativeAngularWeightedSquare s g i)) := by
  have hb (i : AngularIndex) : nativeAngularWeightedSquare s (f-g) i ≤
      2*(nativeAngularWeightedSquare s f i+nativeAngularWeightedSquare s g i) := by
    unfold nativeAngularWeightedSquare
    rw [inner_sub_right]
    nlinarith only [sq_nonneg ((angularEnergyWeight i)^s*
      (inner ℝ (angularBasis i) f+inner ℝ (angularBasis i) g))]
  have hm := (hf.add hg).mul_left 2
  have hs : NativeAngularSpectralRegular s (f-g) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) hb hm
  refine ⟨hs, ?_⟩
  have h := Summable.tsum_le_tsum hb hs hm
  simpa only [tsum_mul_left, hf.tsum_add hg] using h

theorem nativeHighCoupled_cauchy_spectral_regular
    (B W : NativeHighPotential) (d : AngularH1) (n : AngularL2) (s : ℝ)
    (hd : NativeAngularSpectralRegular (s+1) (angularEmbedding d))
    (hn : NativeAngularSpectralRegular s n) :
    let σ := nativeHighCoupledDtNInverse B W (n-B.dtn d)
    NativeAngularSpectralRegular (s+1) (angularEmbedding σ) ∧
      (∑' i, nativeAngularWeightedSquare (s+1) (angularEmbedding σ) i) ≤
        8*((∑' i, nativeAngularWeightedSquare s n i)+
          B.derivativeBound^2*(∑' i, nativeAngularWeightedSquare (s+1) (angularEmbedding d) i)) := by
  obtain ⟨hB,hBb⟩ := B.dtn_spectral_regular d s hd
  obtain ⟨hf,hfb⟩ := nativeAngularSpectralRegular_sub hn hB
  obtain ⟨hs,hsb⟩ := nativeHighCoupled_inverse_spectral_regular B W s (n-B.dtn d) hf
  exact ⟨hs, by linarith only [hBb,hfb,hsb]⟩

#print axioms NativeHighPotential.dtn_weighted_square
#print axioms NativeHighPotential.dtn_spectral_regular
#print axioms nativeAngularSpectralRegular_sub
#print axioms nativeHighCoupled_cauchy_spectral_regular
end Yamabe3.Analysis.Delaunay
