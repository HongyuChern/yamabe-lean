import Yamabe3.Analysis.NativeBoundaryPoissonOperators
import Yamabe3.Analysis.NativeCollarJetValueInjective

/-! The actual coupled same-source boundary correction is now one
bounded linear H2 jet at every scale, with uniform constants chosen
before the potential family. Its entrance is the previous actual jet. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (B P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

private theorem energy_exists :
    ∃D : ℝ,0≤D ∧ ∀F,nativePoissonBoundaryEnergy (nativeFullSourceBoundarySigmaCLM B P hp v hv hb F)≤D*‖F‖^2 := by
  obtain ⟨C,hC,h⟩ := exists_family_nativeFullBoundary_energy P.κ_nonneg P.κ_lt_one (norm_nonneg P.potential)
  exact ⟨C,hC,h B P rfl le_rfl hp v hv hb⟩

def nativeFullBoundaryPoissonRawJetCLM (s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  nativeBoundaryPoissonRawJetCLM P hp (nativeFullSourceBoundarySigmaCLM B P hp v hv hb)
    (fun F => (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1)
    (energy_exists B P hp v hv hb) s

def nativeFullBoundaryPoissonJetCLM (s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  nativeBoundaryPoissonJetCLM P hp (nativeFullSourceBoundarySigmaCLM B P hp v hv hb)
    (fun F => (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1)
    (energy_exists B P hp v hv hb) s

theorem nativeFullBoundaryPoisson_zero (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeFullBoundaryPoissonJetCLM B P hp v hv hb 0 F=
      nativePoissonCollarJet P (nativeFullSourceBoundarySigma B P hp v hv hb F)
        (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1 := by
  let b := nativeFullSourceBoundarySigma B P hp v hv hb F
  have hspec := (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1
  obtain ⟨w,hw,hae,_⟩ := nativePoissonReflectedCurve_joint_representative P b
  have hs := nativePoissonAllScaleValue_same_field P hp b hspec hw.measurable hae 0
  have he := nativePoissonCollarValue_eq_lift P b hspec hw.measurable hae
  apply nativeCollarJet_value_injective
  apply Lp.ext
  have hs0 : (nativePoissonAllScaleValue P hp 0 b : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
    simpa only [mul_zero,zero_div,neg_zero,Real.exp_zero,one_mul,one_smul] using hs
  exact hs0.trans he.symm

private theorem sqrt_bound {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (x : X) (y : Y) {C : ℝ} (hC : 0≤C) (h : ‖y‖^2≤C*‖x‖^2) : ‖y‖≤Real.sqrt C*‖x‖ := by
  have hs : (Real.sqrt C*‖x‖)^2=C*‖x‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  nlinarith [norm_nonneg y,mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg x)]

omit B P hp v hv hb in
theorem exists_family_nativeFullBoundaryPoisson_H2_bounds {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃(C G : ℝ) (K : Fin 3 → ℝ),0≤C ∧ 0≤G ∧ (∀k,0≤K k) ∧
      ∀(B P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀(hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
        (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
        (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (s : ℝ),
      let b := nativeFullSourceBoundarySigma B P hp v hv hb F
      ‖nativePoissonAllScaleValue P hp s b‖≤C*‖F‖ ∧
      (∀j,‖nativePoissonAllScaleFirst P hp s b j‖≤G*‖F‖) ∧
      (∀k j,‖nativePoissonAllScaleSecond P hp s b k j‖≤K k*‖F‖) := by
  obtain ⟨D,hD,he⟩ := exists_family_nativeFullBoundary_energy hκ0 hκ1 hM
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_family_nativePoissonAllScale_H2_bounds hκ0 hκ1 hM
  refine ⟨Real.sqrt (C*D),Real.sqrt (G*D),fun k => Real.sqrt (K k*D),
    Real.sqrt_nonneg _,Real.sqrt_nonneg _,fun k => Real.sqrt_nonneg _,?_⟩
  intro B P hP hPM hp v hv hb F s
  have hh := h P hP hPM hp _ (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1 s
  have he := he B P hP hPM hp v hv hb F
  dsimp only
  refine ⟨sqrt_bound F _ (mul_nonneg hC hD) ?_,fun j => sqrt_bound F _ (mul_nonneg hG hD) ?_,
    fun k j => sqrt_bound F _ (mul_nonneg (hK k) hD) ?_⟩
  · exact hh.1.trans ((mul_le_mul_of_nonneg_left he hC).trans_eq (by ring))
  · exact (hh.2.1 j).trans ((mul_le_mul_of_nonneg_left he hG).trans_eq (by ring))
  · exact (hh.2.2 k j).trans ((mul_le_mul_of_nonneg_left he (hK k)).trans_eq (by ring))

#print axioms nativeFullBoundaryPoissonRawJetCLM
#print axioms nativeFullBoundaryPoisson_zero
#print axioms exists_family_nativeFullBoundaryPoisson_H2_bounds
end Yamabe3.Analysis.SpherePolar
