import Yamabe3.Analysis.NativeFamilyHalfAllScale
import Yamabe3.Analysis.NativeHalfAllScaleGeometricRows

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

theorem exists_family_nativeL2HalfAllScale_raw_jet_bound {κ M : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ B : ℝ,0 < B ∧ ∀ (P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ), ∀ s : ℝ,‖nativeL2HalfAllScaleRawJetCLM P hplus s‖ ≤ B := by
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_family_nativeL2HalfAllScale_H2_bounds hκ0 hκ1 hM
  let L := ∑ k : Fin 3,K k
  have hL : 0 ≤ L := Finset.sum_nonneg (fun k _ => hK k)
  let B := 1+C+G+L
  have hB : 0 < B := by dsimp only [B];linarith
  have hCB : C ≤ B := by dsimp only [B];linarith
  have hGB : G ≤ B := by dsimp only [B];linarith
  have hLB : L ≤ B := by dsimp only [B];linarith
  refine ⟨B,hB,fun P hP hPM hplus s => ContinuousLinearMap.opNorm_le_bound _ hB.le (fun F => ?_)⟩
  have h := h P hP hPM hplus
  have h1 : ‖fun j => nativeL2HalfAllScaleFirst P hplus s F j‖ ≤ G*‖F‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr (h F s).2.1
  have h2 : ‖fun k j => nativeL2HalfAllScaleSecond P hplus s F k j‖ ≤ L*‖F‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    exact ((h F s).2.2 k j).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ => hK i) (Finset.mem_univ k)) (norm_nonneg F))
  change ‖(nativeL2HalfAllScaleValue P hplus s F,
    (fun j => nativeL2HalfAllScaleFirst P hplus s F j),
    (fun k j => nativeL2HalfAllScaleSecond P hplus s F k j))‖ ≤ B*‖F‖
  rw [Prod.norm_def,Prod.norm_def]
  exact max_le ((h F s).1.trans (mul_le_mul_of_nonneg_right hCB (norm_nonneg F)))
    (max_le (h1.trans (mul_le_mul_of_nonneg_right hGB (norm_nonneg F)))
      (h2.trans (mul_le_mul_of_nonneg_right hLB (norm_nonneg F))))
theorem exists_family_nativeL2Half_geometric_row_decay
    {κ M : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M)
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0 < C ∧ ∀ (P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ), ∀ ε : ℝ,0 ≤ ε → ε ≤ 1 → ∀ p ∈ Λ,
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
      (∀ t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀ t,deriv (deriv v) t=radialForce (v t)) → ∀ phase s : ℝ,0 ≤ s →
      ‖nativeL2HalfGeometricRowCLM P hplus (g p) ε v hv phase s‖ ≤ C*ε*Real.exp (-s) := by
  obtain ⟨C,hC,hc⟩ := exists_native_full_collar_error_linear_bound Λ g hB hρ
  obtain ⟨B,hB0,hb⟩ := exists_family_nativeL2HalfAllScale_raw_jet_bound hκ0 hκ1 hM
  refine ⟨C*B,by positivity,fun P hP hPM hplus ε hε hε1 p hp v hv hvb hvo phase s hs => ?_⟩
  have hb := hb P hP hPM hplus
  have he : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  have h := hc (ε*Real.exp (-s)) (by positivity)
    ((mul_le_of_le_one_right hε he).trans hε1) p hp v hv hvb hvo (phase+s)
    (nativeL2HalfAllScaleRawJetCLM P hplus s F)
  have hn := (nativeL2HalfAllScaleRawJetCLM P hplus s).le_of_opNorm_le (hb s) F
  exact (h.trans (mul_le_mul_of_nonneg_left hn (by positivity))).trans_eq (by ring)

#print axioms exists_family_nativeL2HalfAllScale_raw_jet_bound
#print axioms exists_family_nativeL2Half_geometric_row_decay
end Yamabe3.Analysis.SpherePolar
