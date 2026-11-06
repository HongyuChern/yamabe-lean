import Yamabe3.Analysis.BochnerL2NormBound
import Yamabe3.Analysis.BanachFutureInverse
import Mathlib.MeasureTheory.Group.LIntegral

/-! The true one-sided future kernel has exact row and column mass 1/k.
These constants, rather than a lossy symmetric domination, support the
low-mode L2 gap. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def futureL2Kernel (k : ℝ) : ℝ → ℝ := (Iic (0:ℝ)).indicator (fun t => Real.exp (k*t))

theorem futureL2Kernel_nonneg (k t : ℝ) : 0≤futureL2Kernel k t := by
  unfold futureL2Kernel
  exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

theorem futureL2Kernel_measurable (k : ℝ) : Measurable (futureL2Kernel k) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).indicator measurableSet_Iic

theorem futureL2Kernel_mass {k : ℝ} (hk : 0<k) :
    Integrable (futureL2Kernel k) ∧ (∫ t : ℝ,futureL2Kernel k t)=1/k := by
  refine ⟨(integrableOn_exp_mul_Iic hk 0).integrable_indicator measurableSet_Iic,?_⟩
  rw [futureL2Kernel,integral_indicator measurableSet_Iic,integral_exp_mul_Iic hk]
  simp

def futureL2PositiveKernel (k t s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (futureL2Kernel k (t-s))

theorem futureL2PositiveKernel_measurable (k : ℝ) :
    Measurable (Function.uncurry (futureL2PositiveKernel k)) :=
  ((futureL2Kernel_measurable k).comp (measurable_fst.sub measurable_snd)).ennreal_ofReal

theorem futureL2PositiveKernel_mass {k : ℝ} (hk : 0<k) :
    (∀ t : ℝ,(∫⁻ s,futureL2PositiveKernel k t s)=ENNReal.ofReal (1/k)) ∧
    (∀ s : ℝ,(∫⁻ t,futureL2PositiveKernel k t s)=ENNReal.ofReal (1/k)) := by
  have hm : (∫⁻ t : ℝ,ENNReal.ofReal (futureL2Kernel k t))=ENNReal.ofReal (1/k) := by
    rw [←ofReal_integral_eq_lintegral_ofReal (futureL2Kernel_mass hk).1
      (Eventually.of_forall (futureL2Kernel_nonneg k)),(futureL2Kernel_mass hk).2]
  constructor
  · intro t
    unfold futureL2PositiveKernel
    rw [lintegral_sub_left_eq_self (fun x => ENNReal.ofReal (futureL2Kernel k x)) t]
    exact hm
  · intro s
    unfold futureL2PositiveKernel
    rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (futureL2Kernel k x)) s]
    exact hm

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def futureL2Convolution (k : ℝ) (F : ℝ → H) (t : ℝ) : H :=
  ∫ s : ℝ,futureL2Kernel k (t-s) • F s

theorem futureL2Convolution_integrable_memLp {k : ℝ} (hk : 0<k)
    (F : ℝ → H) (hF : StronglyMeasurable F) (hF2 : MemLp F 2) :
    (∀ᵐ t : ℝ,Integrable (fun s => futureL2Kernel k (t-s) • F s)) ∧
      MemLp (futureL2Convolution k F) 2 := by
  have hT : StronglyMeasurable (fun p : ℝ × ℝ => futureL2Kernel k (p.1-p.2) • F p.2) :=
    (((futureL2Kernel_measurable k).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable).smul
      (hF.comp_measurable measurable_snd)
  have hfin : (∫⁻ t : ℝ,‖F t‖ₑ^2)<⊤ := by
    simpa only [ENNReal.toReal_ofNat,ENNReal.rpow_two] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2:ℝ≥0∞)≠0) (by simp) hF2.2)
  apply bochner_kernel_schur_integrable_memLp volume volume (futureL2PositiveKernel_measurable k)
    ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    (fun t => ((futureL2PositiveKernel_mass hk).1 t).le)
    (fun s => ((futureL2PositiveKernel_mass hk).2 s).le) hF.enorm hfin
    (fun t s => futureL2Kernel k (t-s) • F s) hT
  intro t s
  rw [enorm_smul]
  exact le_of_eq (by rw [futureL2PositiveKernel,←ofReal_norm,Real.norm_of_nonneg (futureL2Kernel_nonneg k (t-s))])

theorem futureL2Convolution_eLpNorm_le {k : ℝ} (hk : 0<k)
    (F : ℝ → H) (hF : StronglyMeasurable F) :
    eLpNorm (futureL2Convolution k F) 2≤ENNReal.ofReal (1/k)*eLpNorm F 2 := by
  apply bochner_kernel_eLpNorm_le volume volume (futureL2PositiveKernel_measurable k)
    (fun t => ((futureL2PositiveKernel_mass hk).1 t).le)
    (fun s => ((futureL2PositiveKernel_mass hk).2 s).le) hF
    (fun t s => futureL2Kernel k (t-s) • F s)
  intro t s
  rw [enorm_smul]
  exact le_of_eq (by rw [futureL2PositiveKernel,←ofReal_norm,Real.norm_of_nonneg (futureL2Kernel_nonneg k (t-s))])

theorem futureL2Convolution_congr_ae (k : ℝ) {F G : ℝ → H} (h : F=ᵐ[volume]G) :
    futureL2Convolution k F=futureL2Convolution k G := by
  funext t
  apply integral_congr_ae
  filter_upwards [h] with s hs
  rw [hs]

#print axioms futureL2Kernel_mass
#print axioms futureL2PositiveKernel_mass
#print axioms futureL2Convolution_integrable_memLp
#print axioms futureL2Convolution_eLpNorm_le
#print axioms futureL2Convolution_congr_ae
end Yamabe3.Analysis.Delaunay
