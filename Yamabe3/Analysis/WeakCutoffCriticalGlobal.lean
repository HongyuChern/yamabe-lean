import Yamabe3.Analysis.WeakCutoffCriticalBound

/-! A genuine whole-volume critical source from the annular commutator.
The physical factor eight and zero extension are explicit. Operator
identification with a globally patched field is a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

def physicalCutoffAnnulus (O:Set E) (s a:ℝ):Set E:=
  (fun x:E=>Real.exp (s-Real.log a) • x) ⁻¹' O

def physicalCutoffSource (O:Set E) (χ u:E→ℝ) (s a:ℝ):E→ℝ:=
  (physicalCutoffAnnulus O s a).indicator (fun x:E=>8*Real.exp (-2*Real.log a+s/2)*
    weakCutoffCommutator O χ u (Real.exp (s-Real.log a) • x))

theorem physicalCutoffSource_zero_off_annulus (O:Set E) (χ u:E→ℝ) (s a:ℝ) {x:E}
    (hx:x∉physicalCutoffAnnulus O s a):physicalCutoffSource O χ u s a x=0:=
  indicator_of_notMem hx _

theorem exists_weakCutoff_global_physical_critical_bound {O:Set E} (hO:IsOpen O)
    (hOc:IsCompact (closure O)) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀(u:E→ℝ),MemWkp 1 2 u O→∀(B:ℝ≥0∞) (s a:ℝ),0<a→
      iteratedWeakSobolevNorm 1 2 u O≤ENNReal.ofReal (Real.exp (2*s))*B→
      MemLp (physicalCutoffSource O χ u s a) (6/5:ℝ≥0∞) volume ∧
      eLpNorm (physicalCutoffSource O χ u s a) (6/5:ℝ≥0∞) volume≤C*ENNReal.ofReal (Real.sqrt a)*B := by
  obtain ⟨C,hC,hb⟩:=exists_weakCutoff_scaled_critical_bound hO hOc χ hχ
  refine ⟨8*C,by finiteness,fun u hu B s a ha hn=>?_⟩
  have hh:=hb u hu B s a ha hn
  have hm:MeasurableSet (physicalCutoffAnnulus O s a):=
    (hO.preimage (continuous_id.const_smul (Real.exp (s-Real.log a)))).measurableSet
  have he:(fun x:E=>8*Real.exp (-2*Real.log a+s/2)*weakCutoffCommutator O χ u (Real.exp (s-Real.log a) • x))=
      fun x:E=>8*(Real.exp (-2*Real.log a+s/2)*weakCutoffCommutator O χ u (Real.exp (s-Real.log a) • x)):=by
    funext x;ring
  refine ⟨(memLp_indicator_iff_restrict hm).mpr (he ▸ (hh.1.const_mul 8)),?_⟩
  rw [physicalCutoffSource,eLpNorm_indicator_eq_eLpNorm_restrict hm,he]
  change eLpNorm ((8:ℝ) • (fun x:E=>Real.exp (-2*Real.log a+s/2)*weakCutoffCommutator O χ u (Real.exp (s-Real.log a) • x))) (6/5:ℝ≥0∞) _≤_
  rw [eLpNorm_const_smul]
  norm_num only [Real.enorm_eq_ofReal (by norm_num:(0:ℝ)≤8),ENNReal.ofReal_ofNat]
  exact (mul_le_mul le_rfl hh.2 zero_le zero_le).trans_eq (by ring)

#print axioms physicalCutoffSource_zero_off_annulus
#print axioms exists_weakCutoff_global_physical_critical_bound
end Yamabe3.Analysis.UniformElliptic
