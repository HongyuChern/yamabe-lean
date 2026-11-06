import Yamabe3.Analysis.FutureL2Kernel
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! The true future integral on the L2 quotient, with its sharp norm.
No bounded/continuous representative is assumed of the source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis.Delaunay
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def futureL2Representative (F : Lp H 2 (volume : Measure ℝ)) : ℝ → H :=
  (Lp.memLp F).1.mk F

theorem futureL2Representative_ae (F : Lp H 2 (volume : Measure ℝ)) :
    futureL2Representative F=ᵐ[volume]F := (Lp.memLp F).1.ae_eq_mk.symm

theorem futureL2Representative_memLp (F : Lp H 2 (volume : Measure ℝ)) :
    MemLp (futureL2Representative F) 2 := (Lp.memLp F).ae_eq (futureL2Representative_ae F).symm

def futureL2Resolvent (k : ℝ) (hk : 0<k) (F : Lp H 2 (volume : Measure ℝ)) :
    Lp H 2 (volume : Measure ℝ) :=
  ((futureL2Convolution_integrable_memLp hk (futureL2Representative F)
    (Lp.memLp F).1.stronglyMeasurable_mk (futureL2Representative_memLp F)).2).toLp
      (futureL2Convolution k (futureL2Representative F))

theorem futureL2Resolvent_coe_ae {k : ℝ} (hk : 0<k) (F : Lp H 2 (volume : Measure ℝ)) :
    (futureL2Resolvent k hk F : ℝ → H)=ᵐ[volume]futureL2Convolution k F := by
  have h := ((futureL2Convolution_integrable_memLp hk (futureL2Representative F)
    (Lp.memLp F).1.stronglyMeasurable_mk (futureL2Representative_memLp F)).2).coeFn_toLp
  change (futureL2Resolvent k hk F : ℝ → H)=ᵐ[volume] _ at h
  rwa [futureL2Convolution_congr_ae k (futureL2Representative_ae F)] at h

theorem futureL2Convolution_integrable_Lp {k : ℝ} (hk : 0<k)
    (F : Lp H 2 (volume : Measure ℝ)) :
    ∀ᵐ t : ℝ,Integrable (fun s => futureL2Kernel k (t-s) • F s) := by
  have h := (futureL2Convolution_integrable_memLp hk (futureL2Representative F)
    (Lp.memLp F).1.stronglyMeasurable_mk (futureL2Representative_memLp F)).1
  filter_upwards [h] with t ht
  apply ht.congr
  filter_upwards [futureL2Representative_ae F] with s hs
  rw [hs]

theorem futureL2Resolvent_norm_le {k : ℝ} (hk : 0<k) (F : Lp H 2 (volume : Measure ℝ)) :
    ‖futureL2Resolvent k hk F‖≤(1/k)*‖F‖ := by
  have h := futureL2Convolution_eLpNorm_le hk (futureL2Representative F) (Lp.memLp F).1.stronglyMeasurable_mk
  have ht : ENNReal.ofReal (1/k)*eLpNorm (futureL2Representative F) 2≠⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (futureL2Representative_memLp F).2.ne
  have hr := ENNReal.toReal_mono ht h
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (one_div_nonneg.mpr hk.le),
    eLpNorm_congr_ae (futureL2Representative_ae F)] at hr
  unfold futureL2Resolvent
  rw [Lp.norm_toLp]
  exact hr

theorem futureL2Resolvent_add {k : ℝ} (hk : 0<k) (F G : Lp H 2 (volume : Measure ℝ)) :
    futureL2Resolvent k hk (F+G)=futureL2Resolvent k hk F+futureL2Resolvent k hk G := by
  apply Lp.ext
  have hs := futureL2Resolvent_coe_ae hk (F+G)
  rw [futureL2Convolution_congr_ae k (Lp.coeFn_add F G)] at hs
  filter_upwards [hs,futureL2Resolvent_coe_ae hk F,futureL2Resolvent_coe_ae hk G,
    Lp.coeFn_add (futureL2Resolvent k hk F) (futureL2Resolvent k hk G),
    futureL2Convolution_integrable_Lp hk F,futureL2Convolution_integrable_Lp hk G] with t hs hf hg ho hi hj
  rw [hs,ho,Pi.add_apply,hf,hg]
  change (∫ s : ℝ,futureL2Kernel k (t-s) • (F s+G s))=_
  simp_rw [smul_add]
  exact integral_add hi hj

theorem futureL2Resolvent_smul {k : ℝ} (hk : 0<k) (c : ℝ) (F : Lp H 2 (volume : Measure ℝ)) :
    futureL2Resolvent k hk (c • F)=c • futureL2Resolvent k hk F := by
  apply Lp.ext
  have hs := futureL2Resolvent_coe_ae hk (c • F)
  rw [futureL2Convolution_congr_ae k (Lp.coeFn_smul c F)] at hs
  filter_upwards [hs,futureL2Resolvent_coe_ae hk F,Lp.coeFn_smul c (futureL2Resolvent k hk F)] with t hs hf ho
  rw [hs,ho,Pi.smul_apply,hf]
  change (∫ s : ℝ,futureL2Kernel k (t-s) • (c • F s))=c • _
  simp_rw [smul_comm (futureL2Kernel k (t-_)) c]
  exact integral_smul c _

def futureL2ResolventCLM (k : ℝ) (hk : 0<k) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] Lp H 2 (volume : Measure ℝ) :=
  ({toFun := futureL2Resolvent k hk
    map_add' := futureL2Resolvent_add hk
    map_smul' := futureL2Resolvent_smul hk} :
      Lp H 2 (volume : Measure ℝ) →ₗ[ℝ] Lp H 2 (volume : Measure ℝ)).mkContinuous
    (1/k) (futureL2Resolvent_norm_le hk)

theorem futureL2ResolventCLM_norm {k : ℝ} (hk : 0<k) :
    ‖futureL2ResolventCLM (H := H) k hk‖≤1/k :=
  ContinuousLinearMap.opNorm_le_bound _ (one_div_nonneg.mpr hk.le) (futureL2Resolvent_norm_le hk)

#print axioms futureL2Resolvent_coe_ae
#print axioms futureL2Convolution_integrable_Lp
#print axioms futureL2Resolvent_norm_le
#print axioms futureL2Resolvent_add
#print axioms futureL2Resolvent_smul
#print axioms futureL2ResolventCLM_norm
end Yamabe3.Analysis.Delaunay
