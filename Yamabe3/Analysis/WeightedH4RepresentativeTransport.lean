import Yamabe3.Analysis.WeightedH4Decay

/-! One continuous, C2 away from zero, representative of an all-scale H4
field. Every weighted row remains the literal dilation of that same field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "P" => ({(0:E)}ᶜ : Set E)

theorem weightedPhysicalDilation_congr_ae {u v : E → ℝ} (huv : u =ᵐ[volume] v) (s : ℝ) :
    weightedPhysicalDilation s u =ᵐ[volume.restrict halfEndBasicAnnulus] weightedPhysicalDilation s v := by
  have h : u =ᵐ[volume.restrict univ] v := by simpa only [Measure.restrict_univ] using huv
  have hh := ae_comp_dilation (Real.exp_pos (-s)).ne' h
  have hh' : (fun x => u (Real.exp (-s) • x)) =ᵐ[volume] fun x => v (Real.exp (-s) • x) := by
    simpa only [preimage_univ,Measure.restrict_univ] using hh
  filter_upwards [ae_restrict_of_ae hh'] with x hx
  exact congrArg (fun y : ℝ => Real.exp (3*s/2)*y) hx

theorem weighted_H4_bound_congr_ae {u v : E → ℝ} (huv : u =ᵐ[volume] v)
    {B : ℝ≥0∞}
    (hb : ∀ s : ℝ, -Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ≤ B) :
    ∀ s : ℝ, -Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s v) halfEndBasicAnnulus ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s v) halfEndBasicAnnulus ≤ B := by
  intro s hs
  have he := weightedPhysicalDilation_congr_ae huv s
  refine ⟨(MemWkp_congr_ae (by norm_num) halfEndBasicAnnulus_isOpen he).mp (hb s hs).1,?_⟩
  rw [← wkpNorm_congr_ae (k := 4) (by norm_num) halfEndBasicAnnulus_isOpen he]
  exact (hb s hs).2

theorem exists_continuous_weighted_H4_representative {u : E → ℝ}
    (hu : MemWkpLocally 4 u P) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hb : ∀ s : ℝ, -Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ≤ B) :
    ∃ F : E → ℝ, Continuous F ∧ ContDiffOn ℝ 2 F P ∧ F 0 = 0 ∧ F =ᵐ[volume] u ∧
      ∀ s : ℝ, -Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s F) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s F) halfEndBasicAnnulus ≤ B := by
  have hP : IsOpen P := isClosed_singleton.isOpen_compl
  obtain ⟨G,hG,hGu⟩ := exists_local_weak_H4_C2_representative hP hu
  have hGu' : G =ᵐ[volume] u := by
    have h := (ae_restrict_iff' hP.measurableSet).mp hGu
    filter_upwards [h,volume.ae_ne (0:E)] with x hx hx0
    exact hx hx0
  have hGb := weighted_H4_bound_congr_ae hGu'.symm hb
  obtain ⟨D,hD,hd⟩ := exists_weighted_H4_decay_constant
  have hcont := continuous_zeroAtOrigin hG.continuousOn (mul_nonneg hD ENNReal.toReal_nonneg)
    (hd G hG.continuousOn B hB hGb)
  have he : zeroAtOrigin G =ᵐ[volume] G := by
    filter_upwards [volume.ae_ne (0:E)] with x hx
    exact if_neg hx
  refine ⟨zeroAtOrigin G,hcont,?_,by simp [zeroAtOrigin],he.trans hGu',weighted_H4_bound_congr_ae he.symm hGb⟩
  exact hG.congr (fun x hx => if_neg hx)

#print axioms weightedPhysicalDilation_congr_ae
#print axioms weighted_H4_bound_congr_ae
#print axioms exists_continuous_weighted_H4_representative
end Yamabe3.Analysis.UniformElliptic
