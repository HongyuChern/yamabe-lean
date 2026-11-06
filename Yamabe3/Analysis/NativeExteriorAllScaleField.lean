import Yamabe3.Analysis.NativeExteriorShiftedH2
import Yamabe3.Analysis.NativeAllScaleJetClosure
import Yamabe3.Analysis.NativeAllScaleLocalH2
import Yamabe3.Analysis.NativePoissonExteriorCollarTrace
import Yamabe3.Analysis.NativePoissonExteriorCollarIdentification

/-! One genuine exterior Poisson field on all scales, with the original
entrance jet, actual local H2 regularity and uniform exterior half-end
collar estimates. No homogeneous equation is asserted on the artificial
extension across the entrance. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem nativeExteriorShiftedRawJet_mem (P : NativeHighPotential) (s : ℝ) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    (nativeExteriorShiftedValue P s b,nativeExteriorShiftedFirst P s b,nativeExteriorShiftedSecond P s b)∈nativeCollarJetClosure := by
  have h := nativeExteriorShifted_summable P s b hb
  exact nativeCollarJet_series_mem (fun i => ⟨_,nativeExteriorShiftedMode_C2 P s b i⟩) h.1 h.2.1 h.2.2

def nativeExteriorShiftedJet (P : NativeHighPotential) (s : ℝ) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) : nativeCollarJetClosure :=
  ⟨(nativeExteriorShiftedValue P s b,nativeExteriorShiftedFirst P s b,nativeExteriorShiftedSecond P s b),
    nativeExteriorShiftedRawJet_mem P s b hb⟩

theorem nativeExteriorShiftedJet_zero_eq_original (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativeExteriorShiftedJet P 0 b hb=nativePoissonExteriorCollarJet P b hb := by
  obtain ⟨w,hw,hae,_⟩ := nativePoissonExteriorCurve_joint_representative P b
  have h := nativeExteriorShiftedValue_same_field P 0 b hb hw.measurable hae
  have h0 : (nativeExteriorShiftedValue P 0 b : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
    simpa only [mul_zero,zero_div,neg_zero,Real.exp_zero,one_mul,one_smul] using h
  apply nativeCollarJet_value_injective
  apply Lp.ext
  exact h0.trans (nativePoissonExteriorCollarValue_eq_lift P b hb hw.measurable hae).symm

theorem exists_nativeExteriorPoisson_same_field_localH2 (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    ∃w : ℝ×S→ℝ,Measurable w ∧
      (∀t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativePoissonExteriorCurve P b t : S→ℝ)) ∧
      MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) ∧
      ∀s : ℝ,(nativeExteriorShiftedValue P s b : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) ∧
        MemWkp 2 2 (nativeExteriorShiftedValue P s b) nativePoissonEntranceCollar := by
  obtain ⟨w,hw,hae,_⟩ := nativePoissonExteriorCurve_joint_representative P b
  have hjet (s : ℝ) := nativeExteriorShiftedValue_same_field P s b hb hw.measurable hae
  have hm (s : ℝ) := (nativeExteriorShifted_H2_same_jets P s b hb).1
  have hlocal : MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) :=
    native_all_scale_H2_local (fun s =>
      (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) (hjet s)).mp (hm s))
  exact ⟨w,hw.measurable,hae,hlocal,fun s => ⟨hjet s,hm s⟩⟩

theorem exists_uniform_nativeExteriorPoisson_halfEnd_H2_bounds (P : NativeHighPotential) :
    ∃(C G : ℝ) (K : Fin 3→ℝ),0≤C ∧ 0≤G ∧ (∀k,0≤K k) ∧
      ∀(s : ℝ),s≤0 → ∀(b : AngularH1),NativeAngularSpectralRegular (3/2) (angularEmbedding b) →
        ‖nativeExteriorShiftedValue P s b‖^2≤C*(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) ∧
        (∀j,‖nativeExteriorShiftedFirst P s b j‖^2≤G*(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)) ∧
        (∀k j,‖nativeExteriorShiftedSecond P s b k j‖^2≤K k*(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)) := by
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_nativeExteriorShifted_H2_bounds P
  refine ⟨C,G,K,hC,hG,hK,fun s hs b hb => ?_⟩
  have he : Real.exp (4*s)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hS : 0≤(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := tsum_nonneg (fun i => sq_nonneg _)
  have hbound (D : ℝ) (hD : 0≤D) : (D*Real.exp (4*s))*(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)≤
      D*(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) :=
    mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hD he) hS
  have hh := h s b hb
  exact ⟨hh.1.trans (hbound C hC),fun j => (hh.2.1 j).trans (hbound G hG),
    fun k j => (hh.2.2 k j).trans (hbound (K k) (hK k))⟩

#print axioms nativeExteriorShiftedRawJet_mem
#print axioms nativeExteriorShiftedJet_zero_eq_original
#print axioms exists_nativeExteriorPoisson_same_field_localH2
#print axioms exists_uniform_nativeExteriorPoisson_halfEnd_H2_bounds
end Yamabe3.Analysis.SpherePolar
