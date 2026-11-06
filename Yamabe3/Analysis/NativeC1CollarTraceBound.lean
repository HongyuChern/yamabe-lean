import Yamabe3.Analysis.EuclideanSphereTraceC1
import Yamabe3.Analysis.NativePoissonCollarModes
import Mathlib.Analysis.InnerProductSpace.Dual

/-! A genuine value trace inequality on the actual fixed entrance collar,
for C1 functions, in native round area and Euclidean volume. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

theorem native_fderiv_norm_sq_eq_partials (u : E → ℝ) (x : E) :
    ‖fderiv ℝ u x‖^2 = ∑ j : Fin 3,nativeCoordinateFirst j u x^2 := by
  simpa only [EuclideanSpace.basisFun_apply,nativeCoordinateFirst] using
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual (fderiv ℝ u x)

theorem exists_native_C1_collar_value_trace_bound :
    ∃ C : ℝ,0 ≤ C ∧ ∀ u : E → ℝ,ContDiffOn ℝ 1 u ({0}ᶜ : Set E) →
      (∫ θ : S,u (θ:E)^2 ∂angularVolume) ≤
        C*(∫ x in nativePoissonEntranceCollar,u x^2+∑ j : Fin 3,nativeCoordinateFirst j u x^2) := by
  let a := Real.exp (-(1/4:ℝ))
  let b := Real.exp (1/4:ℝ)
  let K := EuclideanSphereTrace.sphereTraceAnnulus a b
  let V := nativePoissonEntranceCollar
  let L := b-a
  let M := max (1:ℝ) (L^2)
  let C := 2/((b-a)*a^2)
  have ha : 0 < a := Real.exp_pos _
  have hab : a < b := Real.exp_lt_exp.mpr (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hM : 0 ≤ M := (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _)
  have hr : (1:ℝ) ∈ Icc a b := by
    constructor
    · exact (Real.exp_le_one_iff.mpr (by norm_num)).trans le_rfl
    · exact Real.one_le_exp_iff.mpr (by norm_num)
  have hKO : K ⊆ ({0}ᶜ : Set E) := by
    intro x hx
    exact norm_pos_iff.mp (ha.trans_le hx.1)
  have hKV : K ⊆ V := by
    intro x hx
    apply (nativePolarTimeWindow_norm (1/2) x).mpr
    exact ⟨(Real.exp_lt_exp.mpr (by norm_num : (-(1/2:ℝ)) < -(1/4))).trans_le hx.1,
      hx.2.trans_lt (Real.exp_lt_exp.mpr (by norm_num : (1/4:ℝ)<1/2))⟩
  refine ⟨C*M,mul_nonneg hC hM,?_⟩
  intro u hu
  have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have hV : IsOpen V := nativePolarTimeWindow_open (1/2)
  have hVc := nativePolarTimeWindow_precompact (1/2)
  have hVO := nativePolarTimeWindow_closure_offZero (1/2)
  have hLp := native_memLp_two_of_continuousOn_precompact hV.measurableSet hVc hVO hu.continuousOn
  have hp (j : Fin 3) := native_C1_partials_memLp_on_precompact hO hV.measurableSet hVc hVO hu j
  have hE : IntegrableOn (fun x => u x^2+∑ j : Fin 3,nativeCoordinateFirst j u x^2) V :=
    hLp.integrable_sq.add (integrable_finsetSum _ (fun j _ => (hp j).integrable_sq))
  have hec : ContinuousOn (EuclideanSphereTrace.scaledSphereTraceEnergy L u) ({0}ᶜ : Set E) :=
    (hu.continuousOn.pow 2).add (continuousOn_const.mul
      ((hu.continuousOn_fderiv_of_isOpen hO (by norm_num)).norm.pow 2))
  have heI : IntegrableOn (EuclideanSphereTrace.scaledSphereTraceEnergy L u) K := (hec.mono hKO).integrableOn_compact (EuclideanSphereTrace.isCompact_sphereTraceAnnulus a b)
  have hpoint (x : E) : EuclideanSphereTrace.scaledSphereTraceEnergy L u x ≤
      M*(u x^2+∑ j : Fin 3,nativeCoordinateFirst j u x^2) := by
    unfold EuclideanSphereTrace.scaledSphereTraceEnergy
    rw [native_fderiv_norm_sq_eq_partials]
    have h0 := mul_le_mul_of_nonneg_right (show 1≤M from le_max_left _ _) (sq_nonneg (u x))
    have h1 : L^2*(∑ j : Fin 3,nativeCoordinateFirst j u x^2) ≤
        M*(∑ j : Fin 3,nativeCoordinateFirst j u x^2) := mul_le_mul_of_nonneg_right (show L^2≤M from le_max_right _ _)
      (Finset.sum_nonneg (fun j _ => sq_nonneg (nativeCoordinateFirst j u x)))
    nlinarith only [h0,h1]
  have hle := integral_mono heI ((hE.mono_set hKV).const_mul M) hpoint
  rw [integral_const_mul] at hle
  have hinc := setIntegral_mono_set hE (Eventually.of_forall fun x =>
    add_nonneg (sq_nonneg (u x)) (Finset.sum_nonneg (fun j _ => sq_nonneg (nativeCoordinateFirst j u x))))
    (Eventually.of_forall fun x => @hKV x)
  have htrace := EuclideanSphereTrace.integral_sphere_restriction_sq_le_scaled_annulus_energy_C1
    ha hab hr hO hKO hu
  simp only [one_smul,EuclideanSphereTrace.angularVolume,polar_sphereMeasure_eq_native] at htrace
  apply htrace.trans
  have hbound := hle.trans (mul_le_mul_of_nonneg_left hinc hM)
  have hfinal := mul_le_mul_of_nonneg_left hbound hC
  simpa only [C,L,mul_assoc] using hfinal

#print axioms native_fderiv_norm_sq_eq_partials
#print axioms exists_native_C1_collar_value_trace_bound
end Yamabe3.Analysis.SpherePolar
