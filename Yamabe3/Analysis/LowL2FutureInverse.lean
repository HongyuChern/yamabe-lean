import Yamabe3.Analysis.L2BoundedOperatorAction
import Yamabe3.Analysis.StrictLinearFeedback
import Yamabe3.Analysis.NativeAngularLowOperator

/-! A genuine L2 future inverse for the actual low-mode coefficient.
Its 7/8 contraction and norm 2 are uniform in the bounded orbit.
The entrance is not prescribed by this whole-line future construction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction NNReal
namespace Yamabe3.Analysis.Delaunay
open UniformElliptic
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

def doubleFutureL2CLM (k : ℝ) (hk : 0<k) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] Lp H 2 (volume : Measure ℝ) :=
  (futureL2ResolventCLM k hk).comp (futureL2ResolventCLM k hk)

theorem doubleFutureL2CLM_norm {k : ℝ} (hk : 0<k) :
    ‖doubleFutureL2CLM (H := H) k hk‖≤1/k^2 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ (1/k)*(1/k) := mul_le_mul (futureL2ResolventCLM_norm hk)
      (futureL2ResolventCLM_norm hk) (norm_nonneg _) (one_div_nonneg.mpr hk.le)
    _ = _ := by ring

theorem lowL2Future_small (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2) :
    ‖doubleFutureL2CLM (H := H) 2 (by norm_num)‖*‖l2BoundedOperatorActionCLM A‖≤(7/8:ℝ≥0) := by
  have hT : ‖doubleFutureL2CLM (H := H) 2 (by norm_num)‖≤1/4 := by
    simpa only [show (1/(2:ℝ)^2)=1/4 by norm_num] using doubleFutureL2CLM_norm (H := H) (by norm_num : (0:ℝ)<2)
  have hM := (l2BoundedOperatorActionCLM_norm A).trans hA
  exact (mul_le_mul hT hM (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

def lowL2FutureInverseCLM (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] Lp H 2 (volume : Measure ℝ) :=
  strictFeedbackCLM (doubleFutureL2CLM 2 (by norm_num)) (l2BoundedOperatorActionCLM A)
    (q := 7/8) (by norm_num) (lowL2Future_small A hA)

theorem lowL2FutureInverse_fixed (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2)
    (F : Lp H 2 (volume : Measure ℝ)) :
    doubleFutureL2CLM 2 (by norm_num) (F+l2BoundedOperatorActionCLM A (lowL2FutureInverseCLM A hA F))=
      lowL2FutureInverseCLM A hA F :=
  strictFeedback_fixed _ _ (by norm_num : (7/8:ℝ≥0)<1) (lowL2Future_small A hA) F

theorem lowL2FutureInverse_unique (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2)
    (F u : Lp H 2 (volume : Measure ℝ))
    (hu : doubleFutureL2CLM 2 (by norm_num) (F+l2BoundedOperatorActionCLM A u)=u) :
    lowL2FutureInverseCLM A hA F=u := strictFeedback_unique _ _ (by norm_num : (7/8:ℝ≥0)<1) (lowL2Future_small A hA) F u hu

theorem lowL2FutureInverse_norm (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2) :
    ‖lowL2FutureInverseCLM A hA‖≤2 := by
  apply (strictFeedbackCLM_norm _ _ _ _).trans
  have h := doubleFutureL2CLM_norm (H := H) (by norm_num : (0:ℝ)<2)
  norm_num at h ⊢
  linarith

def nativeLowL2FutureInverseCLM (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t,0≤v t ∧ v t≤1) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  lowL2FutureInverseCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb)

theorem nativeLowL2FutureInverse_norm (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t,0≤v t ∧ v t≤1) : ‖nativeLowL2FutureInverseCLM v hv hb‖≤2 :=
  lowL2FutureInverse_norm _ _

#print axioms doubleFutureL2CLM_norm
#print axioms lowL2Future_small
#print axioms lowL2FutureInverse_fixed
#print axioms lowL2FutureInverse_unique
#print axioms lowL2FutureInverse_norm
#print axioms nativeLowL2FutureInverse_norm
end Yamabe3.Analysis.Delaunay
