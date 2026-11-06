import Yamabe3.Analysis.NativeLowCompletionBound
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Resolvent

/-! The canonical zero-entrance remainder of the same full-source field
has a homogeneous H1 completion bound, uniform in the actual orbit and
phase. The low correction is produced by the finite future inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace InnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Weak PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

def nativeHighPhysicalEnergyCoefficient (κ:ℝ) (V:ℝ →ᵇ ℝ) : ℝ :=
  (2/(((5/2:ℝ)^2-4)*(1-κ)^2))^2/6+
    (nativeHalfHighDirichletEnergyBound κ V^2+nativeHalfHighDirichletDerivativeBound κ V^2)/2

theorem fullModelZeroCompletion_norm_sq_bound {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1)
    (p:DelaunayPhaseData κ) (f:HalfEndPhysicalH2SourceGraph) :
    ‖fullModelZeroCompletion hκ0 hκ1 p f‖^2≤
      2*(nativeHighPhysicalEnergyCoefficient κ p.potential+nativeLowZeroEnergyCoefficient)*
        (‖nativeSphereL2Inclusion‖*‖f‖)^2 := by
  let v:ℝ→ℝ:=fun t=>p.orbit (t+p.phase)
  have hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
  have hb:∀t,0≤v t ∧ v t≤1:=fun t=>p.bounded (t+p.phase)
  let F:=halfEndFullSourceAngularCLM f
  let G:=halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f)
  let zHsrc:=nativeHighSourceCylinder G
  let uH:=cylinderLift (fullModelHighJoint hκ0 hκ1 p f)
  let uL:=fullModelLowZeroField p f
  have hO:IsOpen O:=Metric.isOpen_ball.sdiff isClosed_singleton
  have hw:=nativeHalfHighDirichletJoint_measurable hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg
    (halfEndH2SourceToAngularCLM f)
  have hwAE:=nativeHalfHighDirichletJoint_ae hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg
    (halfEndH2SourceToAngularCLM f)
  have hzAE (t:ℝ) : (fun θ=>zHsrc (t,θ)) =ᵐ[angularVolume]
      (nativeHighProjection (halfEndH2SourceToAngularCLM f t.toNNReal):S→ℝ):=by
    have hh:=nativeHighSourceCylinder_ae G t
    change (fun θ=>zHsrc (t,θ)) =ᵐ[angularVolume] (nativeHighProjection (halfEndFullSourceAngularCLM f t):S→ℝ) at hh
    rw [halfEndFullSourceAngular_toNNReal] at hh
    exact hh
  obtain ⟨hH1,-,-,-,dH,hdH,-,-,-,hgrad,-,htotal,hBound⟩:=
    native_forced_halfEnd_global_quantitative_L2_equation hκ0 hκ1 p.potential p.kernel_bound
      p.potential_nonneg (halfEndH2SourceToAngularCLM f) hw zHsrc.continuous.measurable hwAE hzAE
  have hH01:=native_forced_halfEnd_memH01 hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg
    (halfEndH2SourceToAngularCLM f) hw hwAE
  obtain ⟨zH,hzH⟩:=exists_nativeEuclideanH01_of_memH01 hO hH01
  have hnH:‖zH‖^2≤nativeHighPhysicalEnergyCoefficient κ p.potential*‖halfEndH2SourceToAngularCLM f‖^2:=by
    rw [nativeEuclidean_memH01_norm_sq hO hH01 (fun i x=>dH i x) (fun i=>Lp.memLp (dH i)) hdH zH hzH]
    have hi (i:Fin 3):Integrable (fun x=>dH i x^2) (volume.restrict O):=(Lp.memLp (dH i)).integrable_sq
    rw [←integral_finsetSum Finset.univ (fun i _=>hi i),←integral_add hH1.1.integrable_sq hgrad]
    exact hBound
  have hL01:=nativeLowZeroEntranceField_H01 v hv hb F
  obtain ⟨zL,hzL⟩:=exists_nativeEuclideanH01_of_memH01 hO hL01
  have hnL:=nativeLowZeroCompletion_norm_sq v hv hb F zL hzL
  have hsame:fullModelZeroCompletion hκ0 hκ1 p f=zH+zL:=by
    apply toL2_injective («D» := nativeWeakEuclideanD) (Ω := O)
    rw [map_add]
    apply Lp.ext
    simp only [native_euclideanMetric_volumeMeasure]
    have ha:=Lp.coeFn_add (toL2 D O zH) (toL2 D O zL)
    simp only [native_euclideanMetric_volumeMeasure] at ha
    filter_upwards [fullModelZeroCompletion_rep hκ0 hκ1 p f,hzH,hzL,ha] with x hx hh hl ha
    rw [hx,ha,Pi.add_apply,hh,hl]
    by_cases h:x∈O
    · simp only [indicator_of_mem h]
      rfl
    · simp only [indicator_of_notMem h,zero_add]
  have hA:0≤nativeHighPhysicalEnergyCoefficient κ p.potential:=by
    unfold nativeHighPhysicalEnergyCoefficient
    positivity
  have hFh:=halfEndH2SourceToAngularCLM_norm_le f
  have hFl:=halfEndFullSourceAngular_norm_le f
  have h1:‖zH‖^2≤nativeHighPhysicalEnergyCoefficient κ p.potential*(‖nativeSphereL2Inclusion‖*‖f‖)^2:=
    hnH.trans (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hFh) hA)
  have h2:‖zL‖^2≤nativeLowZeroEnergyCoefficient*(‖nativeSphereL2Inclusion‖*‖f‖)^2:=
    hnL.trans (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hFl)
      nativeLowZeroEnergyCoefficient_nonneg)
  rw [hsame]
  have hs:‖zH+zL‖^2≤(‖zH‖+‖zL‖)^2:=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le _ _)
  nlinarith [sq_nonneg (‖zH‖-‖zL‖)]

theorem exists_uniform_full_zero_completion_bound {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) :
    ∃C:ℝ,0≤C ∧ ∀(p:DelaunayPhaseData κ) (f:HalfEndPhysicalH2SourceGraph),
      ‖fullModelZeroCompletion hκ0 hκ1 p f‖≤C*‖f‖ := by
  let e (t:ℝ):=(20/9:ℝ)*(1+(4/9:ℝ)*t/(1-κ))
  let d (t:ℝ):=(10/9:ℝ)*(1+(4/9:ℝ)*t/(1-κ))+(1+(10/9:ℝ)*t/(1-κ))*e t
  let a (t:ℝ):=(2/(((5/2:ℝ)^2-4)*(1-κ)^2))^2/6+((e t+(1+e t*t)*e t)^2+d t^2)/2
  have ha:Continuous a:=by dsimp only [a,d,e];fun_prop
  obtain ⟨B,hB⟩:=(isCompact_Icc (a:=(0:ℝ)) (b:=15/4)).exists_bound_of_continuousOn ha.continuousOn
  let C:=Real.sqrt (2*(max 0 B+nativeLowZeroEnergyCoefficient))*‖nativeSphereL2Inclusion‖
  have hC:0≤C:=mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg nativeSphereL2Inclusion)
  refine ⟨C,hC,?_⟩
  intro p f
  have hp:‖p.potential‖≤15/4:=by
    apply (BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ)≤15/4)).mpr
    intro t
    rw [Real.norm_of_nonneg (p.potential_nonneg t)]
    change (15/4)*p.orbit (t+p.phase)^4≤15/4
    have hh:=pow_le_one₀ (p.bounded (t+p.phase)).1 (p.bounded (t+p.phase)).2 (n:=4)
    linarith
  have hA:nativeHighPhysicalEnergyCoefficient κ p.potential≤ max 0 B:=by
    change a ‖p.potential‖≤ max 0 B
    exact (le_abs_self _).trans ((hB ‖p.potential‖ ⟨norm_nonneg _,hp⟩).trans (le_max_right _ _))
  have hn:=fullModelZeroCompletion_norm_sq_bound hκ0 hκ1 p f
  have hs:‖fullModelZeroCompletion hκ0 hκ1 p f‖^2≤(C*‖f‖)^2:=by
    calc
      _ ≤ 2*(nativeHighPhysicalEnergyCoefficient κ p.potential+nativeLowZeroEnergyCoefficient)*
          (‖nativeSphereL2Inclusion‖*‖f‖)^2:=hn
      _ ≤ 2*(max 0 B+nativeLowZeroEnergyCoefficient)*(‖nativeSphereL2Inclusion‖*‖f‖)^2:=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hA le_rfl) (by norm_num)) (sq_nonneg _)
      _ = _:=by
        dsimp only [C]
        have hlo:=nativeLowZeroEnergyCoefficient_nonneg
        simp only [mul_pow,Real.sq_sqrt (by positivity : 0≤2*(max 0 B+nativeLowZeroEnergyCoefficient))]
        ring
  exact le_of_sq_le_sq hs (mul_nonneg hC (norm_nonneg f))

#print axioms fullModelZeroCompletion_norm_sq_bound
#print axioms exists_uniform_full_zero_completion_bound
end Yamabe3.Analysis.UniformElliptic
