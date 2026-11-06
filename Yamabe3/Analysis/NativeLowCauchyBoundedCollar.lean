import Yamabe3.Analysis.BubbleLowZeroCauchyLinear
import Yamabe3.Analysis.NativeBubbleLowCollar

/-! A bounded linear collar producer for the actual compensated low-mode
Cauchy solution. Its bound is chosen before the two entrance data. It may
depend on the fixed positive entrance time; no phase-uniform bound is claimed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

abbrev NativeLowCauchyCoordinates := (i : {i : AngularIndex // i∈nativeLowIndexFinset}) → ℝ×ℝ

def nativeLowCauchyCoordinateCLM : (AngularL2×AngularL2) →L[ℝ] NativeLowCauchyCoordinates :=
  ContinuousLinearMap.pi fun i =>
    ((innerSL ℝ (angularBasis i.val)).comp (ContinuousLinearMap.fst ℝ AngularL2 AngularL2)).prod
    ((innerSL ℝ (angularBasis i.val)).comp (ContinuousLinearMap.snd ℝ AngularL2 AngularL2))

def nativeLowCauchyQ {t₀ : ℝ} (ht : 0<t₀) (v : NativeLowCauchyCoordinates)
    (i : AngularIndex) : ℝ→ℝ := by
  classical
  exact if hi : i∈nativeLowIndexFinset then bubbleLowZeroCauchyLinear i hi ht (v ⟨i,hi⟩) else 0

theorem nativeLowCauchyQ_C2 {t₀ : ℝ} (ht : 0<t₀) (v : NativeLowCauchyCoordinates)
    (i : AngularIndex) (hi : i∈nativeLowIndexFinset) : ContDiff ℝ 2 (nativeLowCauchyQ ht v i) := by
  rw [nativeLowCauchyQ,dif_pos hi]
  exact (bubbleLowZeroCauchyLinear_spec i hi ht _ _).1

private theorem q_add {t₀ : ℝ} (ht : 0<t₀) (v w : NativeLowCauchyCoordinates) (i : AngularIndex) :
    nativeLowCauchyQ ht (v+w) i=nativeLowCauchyQ ht v i+nativeLowCauchyQ ht w i := by
  by_cases hi : i∈nativeLowIndexFinset
  · simp only [nativeLowCauchyQ,dif_pos hi,Pi.add_apply,map_add]
  · simp only [nativeLowCauchyQ,dif_neg hi,add_zero]

private theorem q_smul {t₀ : ℝ} (ht : 0<t₀) (c : ℝ) (v : NativeLowCauchyCoordinates) (i : AngularIndex) :
    nativeLowCauchyQ ht (c • v) i=c • nativeLowCauchyQ ht v i := by
  by_cases hi : i∈nativeLowIndexFinset
  · simp only [nativeLowCauchyQ,dif_pos hi,Pi.smul_apply,map_smul]
  · simp only [nativeLowCauchyQ,dif_neg hi,smul_zero]

private def physicalLinear {t₀ : ℝ} (ht : 0<t₀) : NativeLowCauchyCoordinates →ₗ[ℝ] (E→ℝ) where
  toFun v := finitePhysical nativeLowIndexFinset (fun i t => nativeLowCauchyQ ht v i (t₀+t))
  map_add' v w := by
    funext x
    simp only [finitePhysical,Pi.add_apply,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : x=0
    · subst x; simp only [cylinderLift_zero,add_zero]
    · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
      change cylinderLift _ (y:E)=cylinderLift _ (y:E)+cylinderLift _ (y:E)
      simp only [cylinderLift_coe,puncturedCylinderLift,separableCylinder,q_add,Pi.add_apply]
      ring
  map_smul' c v := by
    funext x
    simp only [finitePhysical,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : x=0
    · subst x; simp only [cylinderLift_zero,mul_zero]
    · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
      change cylinderLift _ (y:E)=c*cylinderLift _ (y:E)
      simp only [cylinderLift_coe,puncturedCylinderLift,separableCylinder,q_smul,Pi.smul_apply,smul_eq_mul]
      ring

private def c2Linear {t₀ : ℝ} (ht : 0<t₀) : NativeLowCauchyCoordinates →ₗ[ℝ] nativeC2OffZero :=
  (physicalLinear ht).codRestrict nativeC2OffZero fun v =>
    finitePhysical_contDiffOn_offZero_C2 _ _ fun i hi =>
      (nativeLowCauchyQ_C2 ht v i hi).comp (contDiff_const.add contDiff_id)

/-- The actual low collar field, with its first and second weak derivatives. -/
def nativeLowCauchyCollarCLM {t₀ : ℝ} (ht : 0<t₀) :
    (AngularL2×AngularL2) →L[ℝ] nativeCollarJetClosure :=
  (LinearMap.toContinuousLinearMap (nativeC2CollarJetInclusion.comp (c2Linear ht))).comp
    nativeLowCauchyCoordinateCLM

theorem nativeLowCauchyCollarCLM_eq {t₀ : ℝ} (ht : 0<t₀) (d n : AngularL2) :
    nativeLowCauchyCollarCLM ht (d,n)=nativeBubbleLowCollarJet t₀
      (nativeLowCauchyQ ht (nativeLowCauchyCoordinateCLM (d,n)))
      (nativeLowCauchyQ_C2 ht (nativeLowCauchyCoordinateCLM (d,n))) := rfl

theorem nativeLowCauchyCollarCLM_bound {t₀ : ℝ} (ht : 0<t₀) :
    ∃C : ℝ,0<C ∧ ∀d n : AngularL2,
      ‖nativeLowCauchyCollarCLM ht (d,n)‖≤C*max ‖d‖ ‖n‖ := by
  refine ⟨‖nativeLowCauchyCollarCLM ht‖+1,by positivity,?_⟩
  intro d n
  calc
    _ ≤ ‖nativeLowCauchyCollarCLM ht‖*‖(d,n)‖ := (nativeLowCauchyCollarCLM ht).le_opNorm _
    _ ≤ (‖nativeLowCauchyCollarCLM ht‖+1)*max ‖d‖ ‖n‖ := by
      rw [Prod.norm_def]
      exact mul_le_mul_of_nonneg_right (by linarith) (le_max_of_le_left (norm_nonneg _))

#print axioms nativeLowCauchyQ_C2
#print axioms nativeLowCauchyCollarCLM_eq
#print axioms nativeLowCauchyCollarCLM_bound
end Yamabe3.Analysis.SpherePolar
