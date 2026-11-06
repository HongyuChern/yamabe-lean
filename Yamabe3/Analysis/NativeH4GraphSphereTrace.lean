import Yamabe3.Analysis.NativePrincipalErrorValueBound
import Yamabe3.Analysis.NativeC2BoundarySpectral
import Yamabe3.Analysis.NativeSpectralClosedGraph
import Yamabe3.Analysis.NativeCylinderSourceSpace

/-! Literal value and radial derivative of the retained H4 graph function.
Both traces are actual bounded linear maps. Their spectral budgets follow
from proved C2/C1 regularity and closed graph, with constants fixed before
the graph element or the Delaunay phase. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
local notation "O" => ball (0:E) 4 \ {(0:E)}
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2+1))) = 2+1) := ⟨by simp⟩

abbrev nativeH4GraphFunction (v : HalfEndPhysicalH4Graph) : E→ℝ :=
  halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)

theorem nativeH4Graph_sphere_mem (θ : S) : (θ:E)∈O := by
  have hn := norm_eq_of_mem_sphere θ
  exact ⟨by simpa only [mem_ball_zero_iff,hn] using (by norm_num : (1:ℝ)<4),
    by intro h;rw [h,norm_zero] at hn;norm_num at hn⟩

theorem nativeH4Graph_sphere_value_regular (v : HalfEndPhysicalH4Graph) :
    ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 2 (fun θ : S => nativeH4GraphFunction v (θ:E)) := by
  intro θ
  exact ((halfEndPhysicalH4Graph_contDiffOn_two v).contDiffAt
    ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (nativeH4Graph_sphere_mem θ))).contMDiffAt.comp θ
      contMDiff_coe_sphere.contMDiffAt

theorem nativeH4Graph_sphere_normal_regular (v : HalfEndPhysicalH4Graph) :
    ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 (fun θ : S => fderiv ℝ (nativeH4GraphFunction v) (θ:E) (θ:E)) := by
  intro θ
  have h := (halfEndPhysicalH4Graph_contDiffOn_two v).contDiffAt
    ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (nativeH4Graph_sphere_mem θ))
  have hd : ContDiffAt ℝ 1 (fderiv ℝ (nativeH4GraphFunction v)) (θ:E) := h.fderiv_right (by norm_num)
  exact (hd.contMDiffAt.comp θ contMDiff_coe_sphere.contMDiffAt).clm_apply contMDiff_coe_sphere.contMDiffAt

def nativeH4GraphSphereValueLinear : HalfEndPhysicalH4Graph →ₗ[ℝ] C(S,ℝ) where
  toFun v := ⟨fun θ => nativeH4GraphFunction v θ,(nativeH4Graph_sphere_value_regular v).continuous⟩
  map_add' v w := by ext θ; simp only [nativeH4GraphFunction,map_add,halfEndEntranceExtension_add,ContinuousMap.add_apply]; rfl
  map_smul' c v := by ext θ; simp only [nativeH4GraphFunction,map_smul,halfEndEntranceExtension_smul,ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]; rfl

def nativeH4GraphSphereNormalLinear : HalfEndPhysicalH4Graph →ₗ[ℝ] C(S,ℝ) where
  toFun v := ⟨fun θ => fderiv ℝ (nativeH4GraphFunction v) θ θ,(nativeH4Graph_sphere_normal_regular v).continuous⟩
  map_add' v w := by
    ext θ
    have hd (z : HalfEndPhysicalH4Graph) : DifferentiableAt ℝ (nativeH4GraphFunction z) (θ:E) :=
      ((halfEndPhysicalH4Graph_contDiffOn_two z).contDiffAt
        ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (nativeH4Graph_sphere_mem θ))).differentiableAt (by norm_num)
    have he : nativeH4GraphFunction (v+w)=nativeH4GraphFunction v+nativeH4GraphFunction w := by
      funext x; simp only [nativeH4GraphFunction,map_add,halfEndEntranceExtension_add,Pi.add_apply]
    change fderiv ℝ (nativeH4GraphFunction (v+w)) (θ:E) (θ:E)=_
    rw [he,fderiv_add (hd v) (hd w)]
    rfl
  map_smul' c v := by
    ext θ
    have hd : DifferentiableAt ℝ (nativeH4GraphFunction v) (θ:E) :=
      ((halfEndPhysicalH4Graph_contDiffOn_two v).contDiffAt
        ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (nativeH4Graph_sphere_mem θ))).differentiableAt (by norm_num)
    have he : nativeH4GraphFunction (c•v)=c•nativeH4GraphFunction v := by
      funext x; simp only [nativeH4GraphFunction,map_smul,halfEndEntranceExtension_smul,Pi.smul_apply,smul_eq_mul]
    change fderiv ℝ (nativeH4GraphFunction (c•v)) (θ:E) (θ:E)=_
    rw [he,fderiv_const_smul hd]
    rfl

theorem exists_nativeH4Graph_sphere_trace_bound :
    ∃C : ℝ,0≤C ∧ ∀v : HalfEndPhysicalH4Graph,
      ‖nativeH4GraphSphereValueLinear v‖≤C*‖v‖ ∧
      ‖nativeH4GraphSphereNormalLinear v‖≤C*‖v‖ := by
  obtain ⟨C,hC,hb⟩ := exists_uniform_H4_graph_two_jet_bound
  refine ⟨C,hC.le,fun v => ?_⟩
  have he : halfEndWeightedPhysicalSliceMap v.1.1 ⟨0,neg_nonpos.mpr (Real.log_nonneg (by norm_num))⟩=nativeH4GraphFunction v := by
    funext x
    change Real.exp (3*(0:ℝ)/2)*halfEndEntranceExtension v.1.1 (Real.exp (-(0:ℝ)) • x)=_
    simp only [mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul]
    rfl
  have hx (θ : S) : (θ:E)∈halfEndSourceCompactAnnulus := by
    change (3/4:ℝ)≤‖(θ:E)‖ ∧ ‖(θ:E)‖≤3/2
    rw [norm_eq_of_mem_sphere θ]
    norm_num
  have hj (j : ℕ) (hj : j≤2) (θ : S) : ‖iteratedFDeriv ℝ j (nativeH4GraphFunction v) θ‖≤C*‖v‖ := by
    simpa only [he] using hb v ⟨0,neg_nonpos.mpr (Real.log_nonneg (by norm_num))⟩ j hj θ (hx θ)
  constructor
  · apply (ContinuousMap.norm_le _ (mul_nonneg hC.le (norm_nonneg v))).mpr
    intro θ
    change ‖nativeH4GraphFunction v (θ:E)‖≤_
    simpa only [norm_iteratedFDeriv_zero] using hj 0 (by norm_num) θ
  · apply (ContinuousMap.norm_le _ (mul_nonneg hC.le (norm_nonneg v))).mpr
    intro θ
    change ‖fderiv ℝ (nativeH4GraphFunction v) (θ:E) (θ:E)‖≤_
    have hh : ‖fderiv ℝ (nativeH4GraphFunction v) (θ:E)‖≤C*‖v‖ := by
      simpa only [norm_iteratedFDeriv_one] using hj 1 (by norm_num) θ
    exact ((fderiv ℝ (nativeH4GraphFunction v) (θ:E)).le_opNorm (θ:E)).trans
      (by simpa only [norm_eq_of_mem_sphere θ,mul_one] using hh)

def nativeH4GraphSphereValueCLM : HalfEndPhysicalH4Graph →L[ℝ] C(S,ℝ) :=
  nativeH4GraphSphereValueLinear.mkContinuous (Classical.choose exists_nativeH4Graph_sphere_trace_bound)
    (fun v => (Classical.choose_spec exists_nativeH4Graph_sphere_trace_bound).2 v |>.1)

def nativeH4GraphSphereNormalCLM : HalfEndPhysicalH4Graph →L[ℝ] C(S,ℝ) :=
  nativeH4GraphSphereNormalLinear.mkContinuous (Classical.choose exists_nativeH4Graph_sphere_trace_bound)
    (fun v => (Classical.choose_spec exists_nativeH4Graph_sphere_trace_bound).2 v |>.2)

def nativeH4GraphAngularValueCLM : HalfEndPhysicalH4Graph →L[ℝ] AngularL2 :=
  nativeSphereL2Inclusion.comp nativeH4GraphSphereValueCLM

def nativeH4GraphAngularNormalCLM : HalfEndPhysicalH4Graph →L[ℝ] AngularL2 :=
  nativeSphereL2Inclusion.comp nativeH4GraphSphereNormalCLM

theorem nativeSphereL2Inclusion_eq_continuousAngularL2 (f : C(S,ℝ)) :
    nativeSphereL2Inclusion f=continuousAngularL2 f f.continuous := by
  apply Lp.ext
  exact (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _ f).trans
    (by simpa only [Measure.restrict_univ] using (continuousAngularL2_ae f f.continuous).symm)

theorem nativeH4Graph_actual_trace_spectral (v : HalfEndPhysicalH4Graph) :
    NativeAngularSpectralRegular (3/2) (nativeH4GraphAngularValueCLM v) ∧
    NativeAngularSpectralRegular (1/2) (nativeH4GraphAngularNormalCLM v) := by
  change NativeAngularSpectralRegular (3/2) (nativeSphereL2Inclusion (nativeH4GraphSphereValueCLM v)) ∧
    NativeAngularSpectralRegular (1/2) (nativeSphereL2Inclusion (nativeH4GraphSphereNormalCLM v))
  rw [nativeSphereL2Inclusion_eq_continuousAngularL2,nativeSphereL2Inclusion_eq_continuousAngularL2]
  exact ⟨(angular_C2_three_halves_trace _ (nativeH4Graph_sphere_value_regular v)).1,
    (angular_C1_half_trace _ (nativeH4Graph_sphere_normal_regular v)).1⟩

theorem exists_nativeH4Graph_uniform_spectral_trace_bounds :
    ∃C D : ℝ,0≤C ∧ 0≤D ∧ ∀v : HalfEndPhysicalH4Graph,
      (∑'i,nativeAngularWeightedSquare (3/2) (nativeH4GraphAngularValueCLM v) i)≤C*‖v‖^2 ∧
      (∑'i,nativeAngularWeightedSquare (1/2) (nativeH4GraphAngularNormalCLM v) i)≤D*‖v‖^2 := by
  obtain ⟨C,hC,hv⟩ := nativeAngularSpectral_uniform_bound nativeH4GraphAngularValueCLM (3/2)
    (fun v => (nativeH4Graph_actual_trace_spectral v).1)
  obtain ⟨D,hD,hn⟩ := nativeAngularSpectral_uniform_bound nativeH4GraphAngularNormalCLM (1/2)
    (fun v => (nativeH4Graph_actual_trace_spectral v).2)
  exact ⟨C,D,hC,hD,fun v => ⟨hv v,hn v⟩⟩

#print axioms nativeH4Graph_sphere_value_regular
#print axioms nativeH4Graph_sphere_normal_regular
#print axioms exists_nativeH4Graph_sphere_trace_bound
#print axioms nativeH4Graph_actual_trace_spectral
#print axioms exists_nativeH4Graph_uniform_spectral_trace_bounds
end Yamabe3.Analysis.UniformElliptic
