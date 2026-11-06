import Yamabe3.Analysis.SpectralL2Bound
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Realization on the actual L2 quotient, with a strongly measurable
representative, invariance under null-set changes, and the sharp norm bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp
namespace Yamabe3.Analysis.Delaunay

def spectralL2Representative {ι : Type*} (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    ℝ → SpectralSpace ι := (Lp.memLp F).1.mk F

theorem spectralL2Representative_stronglyMeasurable {ι : Type*}
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) : StronglyMeasurable (spectralL2Representative F) :=
  (Lp.memLp F).1.stronglyMeasurable_mk

theorem spectralL2Representative_ae {ι : Type*}
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) : spectralL2Representative F=ᵐ[volume]F :=
  (Lp.memLp F).1.ae_eq_mk.symm

theorem spectralL2Representative_memLp {ι : Type*}
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) : MemLp (spectralL2Representative F) 2 :=
  (Lp.memLp F).ae_eq (spectralL2Representative_ae F).symm

def spectralL2Resolvent {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) : Lp (SpectralSpace ι) 2 (volume : Measure ℝ) :=
  ((spectralL2Convolution_integrable_memLp k hk₀ hk hδ (spectralL2Representative F)
    (spectralL2Representative_stronglyMeasurable F) (spectralL2Representative_memLp F)).2).toLp
      (spectralL2Convolution k hk₀ hk δ (spectralL2Representative F))

theorem spectralL2Resolvent_coe_ae {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    (spectralL2Resolvent k hk₀ hk hδ F : ℝ → SpectralSpace ι)=ᵐ[volume]
      spectralL2Convolution k hk₀ hk δ F := by
  have h := ((spectralL2Convolution_integrable_memLp k hk₀ hk hδ (spectralL2Representative F)
    (spectralL2Representative_stronglyMeasurable F) (spectralL2Representative_memLp F)).2).coeFn_toLp
  change (spectralL2Resolvent k hk₀ hk hδ F : ℝ → SpectralSpace ι)=ᵐ[volume] _ at h
  rw [spectralL2Convolution_congr_ae k hk₀ hk δ (spectralL2Representative_ae F)] at h
  exact h

theorem spectralL2Resolvent_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    ‖spectralL2Resolvent k hk₀ hk hδ F‖ ≤ (1/(k₀^2-δ^2))*‖F‖ := by
  have hb := spectralL2Convolution_eLpNorm_le k hk₀ hk hδ (spectralL2Representative F)
    (spectralL2Representative_stronglyMeasurable F)
  have ht : ENNReal.ofReal (1/(k₀^2-δ^2))*eLpNorm (spectralL2Representative F) 2 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (spectralL2Representative_memLp F).2.ne
  have hr := ENNReal.toReal_mono ht hb
  have hg : 0 ≤ 1/(k₀^2-δ^2) := (one_div_pos.mpr (spectral_gap_positive hk₀ hδ)).le
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hg] at hr
  rw [eLpNorm_congr_ae (spectralL2Representative_ae F)] at hr
  change _ ≤ (1/(k₀^2-δ^2))*‖F‖ at hr
  unfold spectralL2Resolvent
  rw [Lp.norm_toLp]
  exact hr

#print axioms spectralL2Resolvent_coe_ae
#print axioms spectralL2Resolvent_norm_le
end Yamabe3.Analysis.Delaunay
