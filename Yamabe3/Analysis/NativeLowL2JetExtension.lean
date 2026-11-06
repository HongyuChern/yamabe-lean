import Yamabe3.Analysis.NativeLowL2PhysicalLinear
import Yamabe3.Analysis.NativeC2SingleEnergyBounds
import Yamabe3.Analysis.NativeL2ParticularExtension
import Yamabe3.Analysis.NativeCollarJetWeakDerivatives

/-! A genuine uniformly bounded low-mode physical H2 collar solver,
extended from its dense C2 source domain. Its range is the strong C2 jet
closure, so actual weak derivatives and boundary traces are available. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

private theorem sqrt_norm_bound {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (x : X) (y : Y) {C : ℝ} (hC : 0 ≤ C) (h : ‖y‖^2 ≤ C*‖x‖^2) : ‖y‖ ≤ Real.sqrt C*‖x‖ := by
  have hs : (Real.sqrt C*‖x‖)^2=C*‖x‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  have hn : 0 ≤ Real.sqrt C*‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg y]

theorem exists_uniform_nativeLowL2C2Jet_bound :
    ∃ B : ℝ,0 < B ∧ ∀ (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)
      (F : continuousL2Source AngularSpectralSpace),
      ‖nativeLowL2C2JetLinear v hv hb F‖ ≤ B*‖continuousL2SourceInclusion _ F‖ := by
  obtain ⟨G,K,hG,hK,he⟩ := exists_nativeC2Collar_single_energy_bounds
  let C : ℝ := 4*Real.exp 6+(17/2)^2*Real.exp 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let L : ℝ := ∑ k : Fin 3,Real.sqrt (K k*C)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun k _ => Real.sqrt_nonneg _)
  let B := 1+Real.sqrt C+Real.sqrt (G*C)+L
  have hB : 0 < B := by dsimp only [B]; positivity
  have hCB : Real.sqrt C ≤ B := by dsimp only [B];linarith [Real.sqrt_nonneg (G*C)]
  have hGB : Real.sqrt (G*C) ≤ B := by dsimp only [B];linarith [Real.sqrt_nonneg C]
  have hLB : L ≤ B := by dsimp only [B];linarith [Real.sqrt_nonneg C,Real.sqrt_nonneg (G*C)]
  refine ⟨B,hB,fun v hv hb F => ?_⟩
  let u := nativeLowL2PhysicalField v hv hb (continuousL2SourceInclusion _ F)
  have hu := (nativeLowL2Physical_collar_energy v hv hb F.val F.property).1
  have hbound := he u hu (C*‖continuousL2SourceInclusion _ F‖^2) (by positivity)
    (nativeLowL2Physical_collar_energy v hv hb F.val F.property).2.2.2
  have hval : ‖nativeC2CollarValue hu‖ ≤ Real.sqrt C*‖continuousL2SourceInclusion _ F‖ :=
    sqrt_norm_bound _ _ hC hbound.1
  have hfirst (j : Fin 3) : ‖nativeC2CollarFirst hu j‖ ≤ Real.sqrt (G*C)*‖continuousL2SourceInclusion _ F‖ :=
    sqrt_norm_bound _ _ (mul_nonneg hG hC) (by simpa only [mul_assoc] using hbound.2.1 j)
  have hsecond (k j : Fin 3) : ‖nativeC2CollarSecond hu k j‖ ≤ Real.sqrt (K k*C)*‖continuousL2SourceInclusion _ F‖ :=
    sqrt_norm_bound _ _ (mul_nonneg (hK k) hC) (by simpa only [mul_assoc] using hbound.2.2 k j)
  have h1 : ‖fun j => nativeC2CollarFirst hu j‖ ≤ Real.sqrt (G*C)*‖continuousL2SourceInclusion _ F‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr hfirst
  have h2 : ‖fun k j => nativeC2CollarSecond hu k j‖ ≤ L*‖continuousL2SourceInclusion _ F‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    exact (hsecond k j).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ => Real.sqrt_nonneg (K i*C)) (Finset.mem_univ k)) (norm_nonneg _))
  change ‖(nativeC2CollarValue hu,(fun j => nativeC2CollarFirst hu j),(fun k j => nativeC2CollarSecond hu k j))‖ ≤ _
  rw [Prod.norm_def,Prod.norm_def]
  exact max_le (hval.trans (mul_le_mul_of_nonneg_right hCB (norm_nonneg _)))
    (max_le (h1.trans (mul_le_mul_of_nonneg_right hGB (norm_nonneg _)))
      (h2.trans (mul_le_mul_of_nonneg_right hLB (norm_nonneg _))))

def nativeLowL2RawJetCLM (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  (nativeLowL2C2JetLinear v hv hb).extendOfNorm (continuousL2SourceInclusion AngularSpectralSpace)

theorem nativeLowL2RawJet_agrees_continuous (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)
    (F : continuousL2Source AngularSpectralSpace) :
    nativeLowL2RawJetCLM v hv hb (continuousL2SourceInclusion _ F)=nativeLowL2C2JetLinear v hv hb F := by
  obtain ⟨B,hB,h⟩ := exists_uniform_nativeLowL2C2Jet_bound
  exact LinearMap.extendOfNorm_eq (continuousL2SourceInclusion_dense _) ⟨B,h v hv hb⟩ F

theorem exists_uniform_nativeLowL2RawJet_bound :
    ∃ B : ℝ,0 < B ∧ ∀ (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1),
      ‖nativeLowL2RawJetCLM v hv hb‖ ≤ B := by
  obtain ⟨B,hB,h⟩ := exists_uniform_nativeLowL2C2Jet_bound
  refine ⟨B,hB,fun v hv hb => ContinuousLinearMap.opNorm_le_bound _ hB.le (fun F => ?_)⟩
  exact LinearMap.norm_extendOfNorm_apply_le (continuousL2SourceInclusion_dense _) B (h v hv hb) F

theorem nativeLowL2RawJet_mem (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) : nativeLowL2RawJetCLM v hv hb F∈nativeCollarJetClosure := by
  have hc := nativeC2CollarJetLinear.range.isClosed_topologicalClosure.preimage (nativeLowL2RawJetCLM v hv hb).continuous
  refine (continuousL2SourceInclusion_dense AngularSpectralSpace).induction_on F hc ?_
  intro H
  rw [nativeLowL2RawJet_agrees_continuous]
  exact nativeC2CollarJetLinear.range.le_topologicalClosure ⟨nativeLowL2ContinuousFieldLinear v hv hb H,rfl⟩

def nativeLowL2JetCLM (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  (nativeLowL2RawJetCLM v hv hb).codRestrict nativeCollarJetClosure (nativeLowL2RawJet_mem v hv hb)

theorem nativeLowL2Jet_memH2 (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeLowL2RawJetCLM v hv hb F).1 nativePoissonEntranceCollar :=
  nativeCollarJetClosure_memH2 (nativeLowL2JetCLM v hv hb F)

#print axioms exists_uniform_nativeLowL2C2Jet_bound
#print axioms nativeLowL2RawJet_agrees_continuous
#print axioms exists_uniform_nativeLowL2RawJet_bound
#print axioms nativeLowL2RawJet_mem
#print axioms nativeLowL2Jet_memH2
end Yamabe3.Analysis.SpherePolar
