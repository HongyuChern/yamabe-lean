import Yamabe3.Analysis.NativeFreeTailFinite
import Yamabe3.Analysis.NativeC2CollarSeriesNorm

/-! Actual strong sums of free tail fields and their weak jets, with one
constant for all tail scales and all genuine L2 boundary data. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped ENNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativeFreeTailMode (s : ℝ) (b : SpectralSpace AngularIndex) (i : AngularIndex) : E → ℝ :=
  finitePhysical {i} (nativeFreeTailCoefficient s b)

theorem nativeFreeTailMode_C2 (s : ℝ) (b : SpectralSpace AngularIndex) (i : AngularIndex) :
    ContDiffOn ℝ 2 (nativeFreeTailMode s b i) ({0}ᶜ : Set E) :=
  finitePhysical_contDiffOn_offZero_C2 {i} _ (fun j _ => nativeFreeTailCoefficient_C2 s b j)

theorem nativeFreeTailMode_sum (s : ℝ) (b : SpectralSpace AngularIndex) (m : Finset AngularIndex) :
    (fun x => ∑ i ∈ m,nativeFreeTailMode s b i x)=finitePhysical m (nativeFreeTailCoefficient s b) := by
  funext x
  simp [nativeFreeTailMode,finitePhysical]

 theorem spectralSpace_hasSum_square (b : SpectralSpace AngularIndex) : HasSum (fun i => (b i)^2) (‖b‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
    lp.hasSum_norm (by norm_num : 0<(2:ℝ≥0∞).toReal) b

 theorem nativeFreeTailMode_budget (s : ℝ) (hs : 1 ≤ s) (b : SpectralSpace AngularIndex)
    (m : Finset AngularIndex) :
    ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),(∑ i ∈ m,nativeFreeTailMode s b i x)^2)+
      (∫ x in nativePolarTimeWindow (Ioo (-1) 1),
        nativeCoordinateLaplacian (fun y => ∑ i ∈ m,nativeFreeTailMode s b i y) x^2)) ≤
          (2*Real.exp 6)*(∑ i ∈ m,(b i)^2) := by
  have h := nativeFreeTailFinite_energy s hs b m
  simpa only [←nativeFreeTailMode_sum s b m] using h

def nativeFreeTailValue (s : ℝ) (b : SpectralSpace AngularIndex) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarValue (nativeFreeTailMode_C2 s b i)
def nativeFreeTailFirst (s : ℝ) (b : SpectralSpace AngularIndex) (j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarFirst (nativeFreeTailMode_C2 s b i) j
def nativeFreeTailSecond (s : ℝ) (b : SpectralSpace AngularIndex) (k j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarSecond (nativeFreeTailMode_C2 s b i) k j

 theorem nativeFreeTail_summable (s : ℝ) (hs : 1 ≤ s) (b : SpectralSpace AngularIndex) :
    Summable (fun i => nativeC2CollarValue (nativeFreeTailMode_C2 s b i)) ∧
      (∀ j,Summable (fun i => nativeC2CollarFirst (nativeFreeTailMode_C2 s b i) j)) ∧
      (∀ k j,Summable (fun i => nativeC2CollarSecond (nativeFreeTailMode_C2 s b i) k j)) :=
  nativeC2Collar_series_summable _ _ (spectralSpace_hasSum_square b).summable
    (fun i => sq_nonneg _) (by positivity) (nativeFreeTailMode_budget s hs b)

 theorem nativeFreeTail_H2_same_jets (s : ℝ) (hs : 1 ≤ s) (b : SpectralSpace AngularIndex) :
    MemWkp 2 2 (nativeFreeTailValue s b) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativeFreeTailFirst s b j) (nativeFreeTailValue s b) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativeFreeTailSecond s b k j) (nativeFreeTailFirst s b j) nativePoissonEntranceCollar) :=
  nativeC2Collar_series_H2 _ _ (spectralSpace_hasSum_square b).summable
    (fun i => sq_nonneg _) (by positivity) (nativeFreeTailMode_budget s hs b)

 theorem exists_uniform_nativeFreeTail_H2_bounds :
    ∃ (G : ℝ) (K : Fin 3 → ℝ),0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (s : ℝ),1 ≤ s → ∀ b : SpectralSpace AngularIndex,
        ‖nativeFreeTailValue s b‖^2 ≤ (2*Real.exp 6)*‖b‖^2 ∧
        (∀ j,‖nativeFreeTailFirst s b j‖^2 ≤ G*‖b‖^2) ∧
        (∀ k j,‖nativeFreeTailSecond s b k j‖^2 ≤ K k*‖b‖^2) := by
  obtain ⟨G,K,hG,hK,h⟩ := exists_nativeC2Collar_series_norm_bounds (ι := AngularIndex)
  refine ⟨G*(2*Real.exp 6),fun k => K k*(2*Real.exp 6),by positivity,fun k => mul_nonneg (hK k) (by positivity),?_⟩
  intro s hs b
  have he := h _ (nativeFreeTailMode_C2 s b) _ (spectralSpace_hasSum_square b).summable
    (fun i => sq_nonneg _) _ (by positivity) (nativeFreeTailMode_budget s hs b)
  rw [(spectralSpace_hasSum_square b).tsum_eq] at he
  exact he

#print axioms spectralSpace_hasSum_square
#print axioms nativeFreeTail_summable
#print axioms nativeFreeTail_H2_same_jets
#print axioms exists_uniform_nativeFreeTail_H2_bounds
end Yamabe3.Analysis.SpherePolar
