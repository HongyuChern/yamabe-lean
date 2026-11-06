import Yamabe3.Analysis.NativeHighCoupledDtN

/-! The already constructed coupled inverse gains one actual angular
spectral derivative at every real weight. This is a spectral statement;
its identification with geometric fractional trace Sobolev spaces is a
separate obligation and is not inferred from the name of a weight. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def nativeAngularWeightedSquare (s:ℝ) (f:AngularL2) (i:AngularIndex):ℝ:=
  ((angularEnergyWeight i)^s*inner ℝ (angularBasis i) f)^2

def NativeAngularSpectralRegular (s:ℝ) (f:AngularL2):Prop:=
  Summable (nativeAngularWeightedSquare s f)

theorem nativeHighCoupled_inverse_weighted_pointwise
    (B W:NativeHighPotential) (s:ℝ) (f:AngularL2) (i:AngularIndex):
    nativeAngularWeightedSquare (s+1) (angularEmbedding (nativeHighCoupledDtNInverse B W f)) i≤
      4*nativeAngularWeightedSquare s f i:=by
  have hw:0<angularEnergyWeight i:=angularEnergyWeight_pos i
  have hp:0<(angularEnergyWeight i)^s:=Real.rpow_pos_of_pos hw _
  unfold nativeAngularWeightedSquare
  rw [nativeHighCoupledDtNInverse_coefficient,Real.rpow_add hw,Real.rpow_one]
  split_ifs with hi
  · have hB:=B.symbol_lower i hi
    have hW:=W.symbol_lower i hi
    have hsum:0<B.symbol i+W.symbol i:=by linarith
    have hdiv:0≤angularEnergyWeight i/(B.symbol i+W.symbol i):=le_of_lt (div_pos hw hsum)
    have hdiv2:angularEnergyWeight i/(B.symbol i+W.symbol i)≤2:=by
      rw [div_le_iff₀ hsum]
      linarith
    have hsq:(angularEnergyWeight i/(B.symbol i+W.symbol i))^2≤4:=by nlinarith
    have heq:((angularEnergyWeight i)^s*angularEnergyWeight i*
        (inner ℝ (angularBasis i) f/(B.symbol i+W.symbol i)))^2=
        (angularEnergyWeight i/(B.symbol i+W.symbol i))^2*
          ((angularEnergyWeight i)^s*inner ℝ (angularBasis i) f)^2:=by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  · simp only [mul_zero,zero_pow (by norm_num:2≠0)]
    positivity

theorem nativeHighCoupled_inverse_spectral_regular
    (B W:NativeHighPotential) (s:ℝ) (f:AngularL2)
    (hf:NativeAngularSpectralRegular s f):
    NativeAngularSpectralRegular (s+1) (angularEmbedding (nativeHighCoupledDtNInverse B W f)) ∧
      (∑'i,nativeAngularWeightedSquare (s+1) (angularEmbedding (nativeHighCoupledDtNInverse B W f)) i)≤
        4*(∑'i,nativeAngularWeightedSquare s f i):=by
  have hs:Summable (fun i=>4*nativeAngularWeightedSquare s f i):=hf.mul_left 4
  have hb:NativeAngularSpectralRegular (s+1) (angularEmbedding (nativeHighCoupledDtNInverse B W f)):=
    Summable.of_nonneg_of_le (fun i=>sq_nonneg _) (nativeHighCoupled_inverse_weighted_pointwise B W s f) hs
  refine ⟨hb,?_⟩
  rw [←tsum_mul_left]
  exact Summable.tsum_le_tsum (nativeHighCoupled_inverse_weighted_pointwise B W s f) hb hs

/-- The gain needed by an H4 collar starts at the actual 5/2 weighted
normal data, not merely at an unweighted L2 datum. No trace equivalence is
claimed by this spectral corollary. -/
theorem nativeHighCoupled_inverse_five_halves
    (B W:NativeHighPotential) (f:AngularL2) (hf:NativeAngularSpectralRegular (5/2) f):
    NativeAngularSpectralRegular (7/2) (angularEmbedding (nativeHighCoupledDtNInverse B W f)):=by
  convert (nativeHighCoupled_inverse_spectral_regular B W (5/2) f hf).1 using 1 <;> norm_num

#print axioms nativeHighCoupled_inverse_weighted_pointwise
#print axioms nativeHighCoupled_inverse_spectral_regular
#print axioms nativeHighCoupled_inverse_five_halves
end Yamabe3.Analysis.Delaunay
