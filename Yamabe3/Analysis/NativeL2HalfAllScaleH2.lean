import Yamabe3.Analysis.NativePoissonAllScaleH2
import Yamabe3.Analysis.NativeL2HalfCollarCLM

/-! One fixed all-L2 source, its fixed entrance correction, and genuine
weak jets on all scaled collars. The field and entrance are unchanged. -/
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

def nativeL2HalfAllScaleValue (s : ℝ) (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
    (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s)
    (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)-
      nativePoissonAllScaleValue P hplus s (nativeL2HalfEntrance P hplus F)
def nativeL2HalfAllScaleFirst (s : ℝ) (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2ParticularFirstCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
    (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s) j
    (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)-
      nativePoissonAllScaleFirst P hplus s (nativeL2HalfEntrance P hplus F) j
def nativeL2HalfAllScaleSecond (s : ℝ) (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (k j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
    (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s) k j
    (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)-
      nativePoissonAllScaleSecond P hplus s (nativeL2HalfEntrance P hplus F) k j

private theorem weakLp_sub {O : Set E} {j : Fin 3} {u v du dv : Lp ℝ 2 (volume.restrict O)}
    (hu : HasWeakPartialDeriv j du u O) (hv : HasWeakPartialDeriv j dv v O) :
    HasWeakPartialDeriv j ⇑(du-dv) ⇑(u-v) O := by
  simpa only [neg_one_smul,←sub_eq_add_neg] using native_weakPartial_Lp_add hu (native_weakPartial_Lp_smul (-1) hv)

 theorem nativeL2HalfAllScale_H2_same_jets (s : ℝ)
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeL2HalfAllScaleValue P hplus s F) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativeL2HalfAllScaleFirst P hplus s F j)
        (nativeL2HalfAllScaleValue P hplus s F) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativeL2HalfAllScaleSecond P hplus s F k j)
        (nativeL2HalfAllScaleFirst P hplus s F j) nativePoissonEntranceCollar) := by
  have hf := nativeL2ParticularCLM_weak_jets P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
    (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s)
    (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)
  have hc := nativePoissonAllScale_H2_same_jets P hplus s (nativeL2HalfEntrance P hplus F)
    (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F).2.1
  have h1 (j : Fin 3) : HasWeakPartialDeriv j (nativeL2HalfAllScaleFirst P hplus s F j)
      (nativeL2HalfAllScaleValue P hplus s F) nativePoissonEntranceCollar := weakLp_sub (hf.1 j) (hc.2.1 j)
  have h2 (k j : Fin 3) : HasWeakPartialDeriv k (nativeL2HalfAllScaleSecond P hplus s F k j)
      (nativeL2HalfAllScaleFirst P hplus s F j) nativePoissonEntranceCollar := weakLp_sub (hf.2 k j) (hc.2.2 k j)
  refine ⟨?_,h1,h2⟩
  apply memWkp_succ_of_weakDerivatives (nativePolarTimeWindow_open (1/2)) (by norm_num : (1:ℝ≥0∞) ≤ 2)
    (Lp.memLp _) (g := fun j => nativeL2HalfAllScaleFirst P hplus s F j)
  · intro j
    apply MemWkp.one_iff_memW1p.mpr
    exact ⟨Lp.memLp _,fun k => ⟨_,Lp.memLp _,h2 k j⟩⟩
  · exact h1

 theorem nativeL2HalfEntrance_boundary_energy_bound
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativePoissonBoundaryEnergy (nativeL2HalfEntrance P hplus F) ≤
      (2*((50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2))*‖F‖^2 := by
  have h := nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F
  unfold nativePoissonBoundaryEnergy nativeL2HalfEntrance
  nlinarith only [h.2.2.1,h.2.2.2]

private theorem sqrt_bound {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (x : X) (y : Y) {C : ℝ} (hC : 0 ≤ C) (h : ‖y‖^2 ≤ C*‖x‖^2) : ‖y‖ ≤ Real.sqrt C*‖x‖ := by
  have hs : (Real.sqrt C*‖x‖)^2=C*‖x‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  have hn : 0 ≤ Real.sqrt C*‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg y]

 theorem exists_nativeL2HalfAllScale_uniform_H2_bounds :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0 ≤ C ∧ 0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (s : ℝ),
        ‖nativeL2HalfAllScaleValue P hplus s F‖ ≤ C*‖F‖ ∧
        (∀ j,‖nativeL2HalfAllScaleFirst P hplus s F j‖ ≤ G*‖F‖) ∧
        (∀ k j,‖nativeL2HalfAllScaleSecond P hplus s F k j‖ ≤ K k*‖F‖) := by
  obtain ⟨C,G,K,hC,hG,hK,hpart⟩ := exists_nativeL2_all_shifted_collar_uniform_bounds
    P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus
  obtain ⟨D,H,L,hD,hH,hL,hpoisson⟩ := exists_uniform_nativePoissonAllScale_H2_bounds P hplus
  let B := 2*((50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2)
  have hB : 0 ≤ B := by dsimp [B];positivity
  refine ⟨C+Real.sqrt (D*B),G+Real.sqrt (H*B),fun k => K k+Real.sqrt (L k*B),
    by positivity,by positivity,fun k => add_nonneg (hK k) (Real.sqrt_nonneg _),?_⟩
  intro F s
  have hp := hpart F s
  have hz := hpoisson (nativeL2HalfEntrance P hplus F)
    (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F).2.1 s
  have hb := nativeL2HalfEntrance_boundary_energy_bound P hplus F
  have h0 := sqrt_bound F _ (mul_nonneg hD hB)
    (hz.1.trans ((mul_le_mul_of_nonneg_left hb hD).trans_eq (by ring)))
  have h1 (j : Fin 3) := sqrt_bound F _ (mul_nonneg hH hB)
    ((hz.2.1 j).trans ((mul_le_mul_of_nonneg_left hb hH).trans_eq (by ring)))
  have h2 (k j : Fin 3) := sqrt_bound F _ (mul_nonneg (hL k) hB)
    ((hz.2.2 k j).trans ((mul_le_mul_of_nonneg_left hb (hL k)).trans_eq (by ring)))
  exact ⟨(norm_sub_le _ _).trans ((add_le_add hp.1 h0).trans_eq (by ring)),
    fun j => (norm_sub_le _ _).trans ((add_le_add (hp.2.1 j) (h1 j)).trans_eq (by ring)),
    fun k j => (norm_sub_le _ _).trans ((add_le_add (hp.2.2 k j) (h2 k j)).trans_eq (by ring))⟩

#print axioms nativeL2HalfAllScale_H2_same_jets
#print axioms nativeL2HalfEntrance_boundary_energy_bound
#print axioms exists_nativeL2HalfAllScale_uniform_H2_bounds
end Yamabe3.Analysis.SpherePolar
