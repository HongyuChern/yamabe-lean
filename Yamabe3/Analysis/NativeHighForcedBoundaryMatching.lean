import Yamabe3.Analysis.NativeBubbleDelaunayCoupling
import Yamabe3.Analysis.NativeForcedHalfEndDerivativeOperator

/-! Same-source high exterior particular field and the actual coupled
Cauchy correction. The particular normal trace is produced by the
constructed Dirichlet inverse, not supplied as an arbitrary functional. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum


def NativeHighPotential.forcedCurve (P:NativeHighPotential) (F:ℝ≥0 →ᵇ AngularL2):ℝ→AngularL2:=
  nativeHalfHighDirichletPhysical P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg F

def NativeHighPotential.forcedLeftDerivative (P:NativeHighPotential) (F:ℝ≥0 →ᵇ AngularL2):AngularL2:=
  -nativeHalfHighDirichletEntranceDerivativeCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg F

theorem NativeHighPotential.forcedCurve_zero (P:NativeHighPotential) (F:ℝ≥0 →ᵇ AngularL2):P.forcedCurve F 0=0:=
  nativeHalfHighDirichletPhysical_zero_of_nonpos P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg F 0 le_rfl

theorem NativeHighPotential.forcedLeftDerivative_high (P:NativeHighPotential) (F:ℝ≥0 →ᵇ AngularL2):
    nativeHighProjection (P.forcedLeftDerivative F)=P.forcedLeftDerivative F:=by
  have hd:=nativeHalfHighDirichletEntranceDerivativeCLM_hasDerivWithinAt
    P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg F
  have hp:=nativeHighProjection.hasFDerivAt.comp_hasDerivWithinAt 0 hd
  have he:HasDerivWithinAt (P.forcedCurve F)
      (nativeHighProjection (nativeHalfHighDirichletEntranceDerivativeCLM
        P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg F)) (Ici 0) 0:=by
    apply hp.congr_of_mem _ (mem_Ici.mpr le_rfl)
    intro t ht
    exact (nativeHalfHighDirichletPhysical_high P.κ_nonneg P.κ_lt_one P.potential
      P.kernel_bound P.nonneg F t).symm
  have hh:=(uniqueDiffWithinAt_Ici (0:ℝ)).eq_deriv _ he hd
  simpa only [NativeHighPotential.forcedLeftDerivative,map_neg] using congrArg Neg.neg hh

theorem NativeHighPotential.forcedLeftDerivative_bound (P:NativeHighPotential) (F:ℝ≥0 →ᵇ AngularL2):
    ‖P.forcedLeftDerivative F‖≤nativeHalfHighDirichletDerivativeBound P.κ P.potential*‖F‖:=by
  rw [NativeHighPotential.forcedLeftDerivative,norm_neg]
  exact nativeHalfHighDirichletEntranceDerivativeCLM_norm_le
    P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg F

theorem NativeHighPotential.forcedCurve_left_derivative (P:NativeHighPotential) (F:ℝ≥0 →ᵇ AngularL2):
    HasDerivWithinAt (fun t:ℝ=>P.forcedCurve F (-t)) (P.forcedLeftDerivative F) (Iic 0) 0:=by
  have hd:=nativeHalfHighDirichletEntranceDerivativeCLM_hasDerivWithinAt
    P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg F
  have h:=hd.scomp_of_eq 0 (hasDerivAt_id (0:ℝ)).neg.hasDerivWithinAt
    (show MapsTo (fun t:ℝ=> -t) (Iic 0) (Ici 0) from fun t ht=>mem_Ici.mpr (neg_nonneg.mpr ht)) (by simp)
  simpa only [Function.comp_def,Pi.neg_apply,id_eq,neg_smul,one_smul,NativeHighPotential.forcedLeftDerivative,NativeHighPotential.forcedCurve] using h

theorem NativeHighPotential.forcedCurve_source_equation (P:NativeHighPotential) (F:ℝ≥0 →ᵇ AngularL2)
    (i:AngularIndex) (t:ℝ) (ht:0<t):
    deriv (deriv (fun s=>inner ℝ (angularBasis i) (P.forcedCurve F s))) t=
      (angularEigenvalue i+1/4-P.potential t)*inner ℝ (angularBasis i) (P.forcedCurve F t)+
        Real.exp (-2*t)*inner ℝ (angularBasis i) (nativeHighProjection (F t.toNNReal)):=
  (nativeHalfHighDirichletPhysical_coefficient_equation P.κ_nonneg P.κ_lt_one P.potential
    P.kernel_bound P.nonneg F i t ht).deriv


/-- The real particular solution, its produced normal trace and the
same sigma solve both model high Cauchy equations. -/
theorem exists_actual_high_forced_cauchy_matching (B W:NativeHighPotential)
    (F:ℝ≥0 →ᵇ AngularL2) (d:AngularH1) (hd:nativeHighEnergyProjectionCLM d=d)
    (n:AngularL2) (hn:nativeHighProjection n=n):
    ∃σ:AngularH1,nativeHighEnergyProjectionCLM σ=σ ∧
      B.forcedCurve F 0+B.curve (σ+d) 0-W.curve σ 0=angularEmbedding d ∧
      HasDerivWithinAt (fun t:ℝ=>B.forcedCurve F (-t)+B.curve (σ+d) (-t))
        (B.forcedLeftDerivative F+B.dtn (σ+d)) (Iic 0) 0 ∧
      HasDerivWithinAt (W.curve σ) (-W.dtn σ) (Ici 0) 0 ∧
      (B.forcedLeftDerivative F+B.dtn (σ+d))-(-W.dtn σ)=n:=by
  have hsource:nativeHighProjection (n-B.forcedLeftDerivative F)=n-B.forcedLeftDerivative F:=by
    rw [map_sub,hn,B.forcedLeftDerivative_high]
  obtain ⟨σ,hs,hv,ho,hi,he⟩:=exists_actual_high_poisson_cauchy_matching
    B W d hd (n-B.forcedLeftDerivative F) hsource
  refine ⟨σ,hs,?_,(B.forcedCurve_left_derivative F).add ho,hi,?_⟩
  · rw [B.forcedCurve_zero,zero_add]
    exact hv
  · rw [add_sub_assoc,he]
    abel

#print axioms NativeHighPotential.forcedLeftDerivative_high
#print axioms NativeHighPotential.forcedLeftDerivative_bound
#print axioms NativeHighPotential.forcedCurve_left_derivative
#print axioms NativeHighPotential.forcedCurve_source_equation
#print axioms exists_actual_high_forced_cauchy_matching
end Yamabe3.Analysis.Delaunay
