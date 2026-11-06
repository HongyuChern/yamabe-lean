import Yamabe3.Analysis.AngularNormalJetBudget
import Yamabe3.Analysis.NativeH4GraphSphereTrace

/-! Actual linear sphere traces of one locally smooth linear field.
Point values and normal derivatives are constructed before taking their
L2 classes. Quantitative spectral costs use the same two-jet bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal RealInnerProductSpace lp
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay Poincare.Geometry.Riemannian.SpaceForm
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
local instance : Fact (Module.finrank ℝ E=2+1) := ⟨by simp [E]⟩

private theorem sphere_mem_ball_three (θ : S) : (θ:E)∈ball (0:E) 3 := by
  rw [mem_ball_zero_iff,norm_eq_of_mem_sphere θ]
  norm_num

def localLinearSphereValue (P : X →ₗ[ℝ] (E→ℝ))
    (hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E) 3)) : X →ₗ[ℝ] C(S,ℝ) where
  toFun W := ⟨fun θ => P W θ,by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact ((hP W).continuousOn.continuousAt (isOpen_ball.mem_nhds (sphere_mem_ball_three θ))).comp
      continuous_subtype_val.continuousAt⟩
  map_add' W Z := by
    ext θ
    change P (W+Z) (θ:E)=P W (θ:E)+P Z (θ:E)
    exact congrFun (map_add P W Z) (θ:E)
  map_smul' c W := by
    ext θ
    change P (c • W) (θ:E)=c • P W (θ:E)
    exact congrFun (map_smul P c W) (θ:E)

def localLinearSphereNormal (P : X →ₗ[ℝ] (E→ℝ))
    (hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E) 3)) : X →ₗ[ℝ] C(S,ℝ) where
  toFun W := ⟨fun θ => fderiv ℝ (P W) θ θ,by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hc := (hP W).contDiffAt (isOpen_ball.mem_nhds (sphere_mem_ball_three θ))
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ (P W)) (θ:E) := hc.fderiv_right (by simp)
    exact (hd.continuousAt.comp continuous_subtype_val.continuousAt).clm_apply
      continuous_subtype_val.continuousAt⟩
  map_add' W Z := by
    ext θ
    change fderiv ℝ (P (W+Z)) (θ:E) (θ:E)=_
    rw [map_add,fderiv_add]
    · rfl
    · exact ((hP W).contDiffAt (isOpen_ball.mem_nhds (sphere_mem_ball_three θ))).differentiableAt (by simp)
    · exact ((hP Z).contDiffAt (isOpen_ball.mem_nhds (sphere_mem_ball_three θ))).differentiableAt (by simp)
  map_smul' c W := by
    ext θ
    change fderiv ℝ (P (c • W)) (θ:E) (θ:E)=_
    rw [map_smul,fderiv_const_smul]
    · rfl
    · exact ((hP W).contDiffAt (isOpen_ball.mem_nhds (sphere_mem_ball_three θ))).differentiableAt (by simp)

theorem exists_localLinearSphere_trace_maps (P : X →ₗ[ℝ] (E→ℝ))
    (hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E) 3))
    (C : ℝ) (hC : 0≤C)
    (hb : ∀W,∀j≤2,∀x∈closedBall (0:E) 2,‖iteratedFDeriv ℝ j (P W) x‖≤C*‖W‖) :
    ∃(T N : X →L[ℝ] AngularL2),
      (∀W,T W=nativeSphereL2Inclusion (localLinearSphereValue P hP W)) ∧
      (∀W,N W=nativeSphereL2Inclusion (localLinearSphereNormal P hP W)) ∧
      ‖T‖≤‖nativeSphereL2Inclusion‖*C ∧ ‖N‖≤‖nativeSphereL2Inclusion‖*C ∧
      ∀W,NativeAngularSpectralRegular (3/2) (T W) ∧ NativeAngularSpectralRegular (1/2) (N W) ∧
        (∑'i,nativeAngularWeightedSquare (3/2) (T W) i)≤
          74*((roundSphereMetric 2).volumeMeasure univ).toReal*(C*‖W‖)^2 ∧
        (∑'i,nativeAngularWeightedSquare (1/2) (N W) i)≤
          5*((roundSphereMetric 2).volumeMeasure univ).toReal*(C*‖W‖)^2 := by
  have hx (θ : S) : (θ:E)∈closedBall (0:E) 2 := by
    rw [mem_closedBall,dist_zero_right,norm_eq_of_mem_sphere θ];norm_num
  have hval W : ‖localLinearSphereValue P hP W‖≤C*‖W‖ := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg W))).mpr
    intro θ
    simpa only [localLinearSphereValue,LinearMap.coe_mk,AddHom.coe_mk,ContinuousMap.coe_mk,
      norm_iteratedFDeriv_zero] using hb W 0 (by norm_num) θ (hx θ)
  have hnormal W : ‖localLinearSphereNormal P hP W‖≤C*‖W‖ := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg W))).mpr
    intro θ
    change ‖fderiv ℝ (P W) (θ:E) (θ:E)‖≤_
    have hd : ‖fderiv ℝ (P W) (θ:E)‖≤C*‖W‖ := by
      simpa only [norm_iteratedFDeriv_one] using hb W 1 (by norm_num) θ (hx θ)
    exact ((fderiv ℝ (P W) (θ:E)).le_opNorm (θ:E)).trans (by
      simpa only [norm_eq_of_mem_sphere θ,mul_one] using hd)
  let Tv := (localLinearSphereValue P hP).mkContinuous C hval
  let Nv := (localLinearSphereNormal P hP).mkContinuous C hnormal
  let T := nativeSphereL2Inclusion.comp Tv
  let N := nativeSphereL2Inclusion.comp Nv
  refine ⟨T,N,fun W => rfl,fun W => rfl,?_,?_,fun W => ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (LinearMap.mkContinuous_norm_le _ hC hval) (norm_nonneg _))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (LinearMap.mkContinuous_norm_le _ hC hnormal) (norm_nonneg _))
  have hs : ∀θ:S,ContDiffAt ℝ ∞ (P W) (θ:E) :=
    fun θ => (hP W).contDiffAt (isOpen_ball.mem_nhds (sphere_mem_ball_three θ))
  have hj : ∀j≤2,∀θ:S,‖iteratedFDeriv ℝ j (P W) θ‖≤C*‖W‖ :=
    fun j hj θ => hb W j hj θ (hx θ)
  obtain ⟨hv,hvr,hvb⟩ := angular_three_halves_budget_of_ambient_jets hs (mul_nonneg hC (norm_nonneg W)) hj
  obtain ⟨hn,hnr,hnb⟩ := angular_half_normal_budget_of_ambient_jets hs (mul_nonneg hC (norm_nonneg W)) hj
  have ht : T W=continuousAngularL2 (fun θ:S => P W θ) hv.continuous :=
    nativeSphereL2Inclusion_eq_continuousAngularL2 _
  have hnt : N W=continuousAngularL2 (fun θ:S => fderiv ℝ (P W) θ θ) hn.continuous :=
    nativeSphereL2Inclusion_eq_continuousAngularL2 _
  rw [ht,hnt]
  exact ⟨hvr,hnr,hvb,hnb⟩

#print axioms localLinearSphereValue
#print axioms localLinearSphereNormal
#print axioms exists_localLinearSphere_trace_maps
end Yamabe3.Analysis.UniformElliptic
