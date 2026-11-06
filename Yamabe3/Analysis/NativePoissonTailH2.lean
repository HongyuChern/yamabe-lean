import Yamabe3.Analysis.NativePoissonL2Decomposition
import Yamabe3.Analysis.SpectralBoundaryPoissonL2Bound
import Yamabe3.Analysis.NativeCollarLocalSlices

/-! Genuine H2 jets of the original potential Poisson field on every
tail collar, as the same free field minus its one L2 correction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)

def nativePoissonTailValue (s : ℝ) (b : AngularH1) : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeFreeTailValue s (nativePoissonAuxiliary P b)-
    nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s)
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s (nativePoissonL2CorrectionSource P b))
def nativePoissonTailFirst (s : ℝ) (b : AngularH1) (j : Fin 3) : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeFreeTailFirst s (nativePoissonAuxiliary P b) j-
    nativeL2ParticularFirstCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s) j
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s (nativePoissonL2CorrectionSource P b))
def nativePoissonTailSecond (s : ℝ) (b : AngularH1) (k j : Fin 3) : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeFreeTailSecond s (nativePoissonAuxiliary P b) k j-
    nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s) k j
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s (nativePoissonL2CorrectionSource P b))

private theorem weakLp_sub {O : Set E} {j : Fin 3}
    {u v du dv : Lp ℝ 2 (volume.restrict O)}
    (hu : HasWeakPartialDeriv j du u O) (hv : HasWeakPartialDeriv j dv v O) :
    HasWeakPartialDeriv j (du-dv : Lp ℝ 2 (volume.restrict O)) (u-v : Lp ℝ 2 (volume.restrict O)) O := by
  simpa only [neg_one_smul,←sub_eq_add_neg] using native_weakPartial_Lp_add hu (native_weakPartial_Lp_smul (-1) hv)

 theorem nativePoissonTail_H2_same_jets (s : ℝ) (hs : 1 ≤ s) (b : AngularH1) :
    MemWkp 2 2 (nativePoissonTailValue P hplus s b) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativePoissonTailFirst P hplus s b j)
        (nativePoissonTailValue P hplus s b) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativePoissonTailSecond P hplus s b k j)
        (nativePoissonTailFirst P hplus s b j) nativePoissonEntranceCollar) := by
  have hf := nativeFreeTail_H2_same_jets s hs (nativePoissonAuxiliary P b)
  have hc := nativeL2ParticularCLM_weak_jets P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
    (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s)
    (l2TimeTranslateCLM (SpectralSpace AngularIndex) s (nativePoissonL2CorrectionSource P b))
  have h1 (j : Fin 3) : HasWeakPartialDeriv j (nativePoissonTailFirst P hplus s b j)
      (nativePoissonTailValue P hplus s b) nativePoissonEntranceCollar := weakLp_sub (hf.2.1 j) (hc.1 j)
  have h2 (k j : Fin 3) : HasWeakPartialDeriv k (nativePoissonTailSecond P hplus s b k j)
      (nativePoissonTailFirst P hplus s b j) nativePoissonEntranceCollar := weakLp_sub (hf.2.2 k j) (hc.2 k j)
  refine ⟨?_,h1,h2⟩
  apply memWkp_succ_of_weakDerivatives (nativePolarTimeWindow_open (1/2)) (by norm_num : (1:ℝ≥0∞) ≤ 2)
    (Lp.memLp _) (g := fun j => nativePoissonTailFirst P hplus s b j)
  · intro j
    apply MemWkp.one_iff_memW1p.mpr
    exact ⟨Lp.memLp _,fun k => ⟨_,Lp.memLp _,h2 k j⟩⟩
  · exact h1

 theorem nativePoissonAuxiliary_norm_le (b : AngularH1) : ‖nativePoissonAuxiliary P b‖ ≤ ‖b‖ := by
  rw [nativePoissonAuxiliary,LinearIsometryEquiv.norm_map]
  exact (PoincareMT.LeviCivitaData.Dirichlet.norm_toDomainL2_le _).trans
    (nativeHighEnergyEntranceCLM_norm_le P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg b)

 theorem exists_nativePoissonL2CorrectionSource_bound :
    ∃ C : ℝ,0 ≤ C ∧ ∀ b : AngularH1,‖nativePoissonL2CorrectionSource P b‖ ≤ C*‖b‖ := by
  obtain ⟨C,hC,h⟩ := exists_spectralBoundaryPotentialSource_L2_bound nativeAngularRate
    (by norm_num) nativeAngularRate_lower P.potential
  exact ⟨C,hC,fun b => (h (nativePoissonAuxiliary P b)).trans
    (mul_le_mul_of_nonneg_left (nativePoissonAuxiliary_norm_le P b) hC)⟩

private theorem sqrt_bound {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (x : X) (y : Y) {C : ℝ} (hC : 0 ≤ C) (h : ‖y‖^2 ≤ C*‖x‖^2) : ‖y‖ ≤ Real.sqrt C*‖x‖ := by
  have hs : (Real.sqrt C*‖x‖)^2=C*‖x‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  have hn : 0 ≤ Real.sqrt C*‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg y]

 theorem exists_uniform_nativePoissonTail_H2_bounds :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0 ≤ C ∧ 0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (s : ℝ),1 ≤ s → ∀ b : AngularH1,
        ‖nativePoissonTailValue P hplus s b‖ ≤ C*‖b‖ ∧
        (∀ j,‖nativePoissonTailFirst P hplus s b j‖ ≤ G*‖b‖) ∧
        (∀ k j,‖nativePoissonTailSecond P hplus s b k j‖ ≤ K k*‖b‖) := by
  obtain ⟨G,K,hG,hK,hfree⟩ := exists_uniform_nativeFreeTail_H2_bounds
  obtain ⟨C0,C1,C2,hC0,hC1,hC2,hcorr⟩ := exists_nativeL2_all_shifted_collar_uniform_bounds
    P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus
  obtain ⟨B,hB,hb⟩ := exists_nativePoissonL2CorrectionSource_bound P
  refine ⟨Real.sqrt (2*Real.exp 6)+C0*B,Real.sqrt G+C1*B,fun k => Real.sqrt (K k)+C2 k*B,
    by positivity,by positivity,fun k => add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hC2 k) hB),?_⟩
  intro s hs b
  have hf := hfree s hs (nativePoissonAuxiliary P b)
  have hc := hcorr (nativePoissonL2CorrectionSource P b) s
  have hF0 := (sqrt_bound _ _ (by positivity) hf.1).trans
    (mul_le_mul_of_nonneg_left (nativePoissonAuxiliary_norm_le P b) (Real.sqrt_nonneg _))
  have hF1 (j : Fin 3) := (sqrt_bound _ _ hG (hf.2.1 j)).trans
    (mul_le_mul_of_nonneg_left (nativePoissonAuxiliary_norm_le P b) (Real.sqrt_nonneg _))
  have hF2 (k j : Fin 3) := (sqrt_bound _ _ (hK k) (hf.2.2 k j)).trans
    (mul_le_mul_of_nonneg_left (nativePoissonAuxiliary_norm_le P b) (Real.sqrt_nonneg _))
  refine ⟨?_,fun j => ?_,fun k j => ?_⟩
  · exact (norm_sub_le _ _).trans ((add_le_add hF0
      (hc.1.trans (mul_le_mul_of_nonneg_left (hb b) hC0))).trans_eq (by ring))
  · exact (norm_sub_le _ _).trans ((add_le_add (hF1 j)
      ((hc.2.1 j).trans (mul_le_mul_of_nonneg_left (hb b) hC1))).trans_eq (by ring))
  · exact (norm_sub_le _ _).trans ((add_le_add (hF2 k j)
      ((hc.2.2 k j).trans (mul_le_mul_of_nonneg_left (hb b) (hC2 k)))).trans_eq (by ring))

#print axioms nativePoissonTail_H2_same_jets
#print axioms nativePoissonAuxiliary_norm_le
#print axioms exists_nativePoissonL2CorrectionSource_bound
#print axioms exists_uniform_nativePoissonTail_H2_bounds
end Yamabe3.Analysis.SpherePolar
