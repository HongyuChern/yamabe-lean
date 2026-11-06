import Yamabe3.Analysis.NativeFullWeightedEquation
import Yamabe3.Analysis.NativeWeightedLift
import PoincareLib.Analysis.Sobolev.Euclidean.L2

/-! Uniform weighted L2 of the same complete high-plus-low field.
The low angular projection is used only as an L2 contraction here;
no H2 projection bound is postulated. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum

theorem exists_full_weighted_shell_L2_bound
    {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (a b:ℝ) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀(p:DelaunayPhaseData κ) (f:HalfEndPhysicalH2SourceGraph) (s:ℝ),
      MemLp (actualWeightedFullModelField hκ0 hκ1 p f s) 2 (volume.restrict (cylinderShell a b)) ∧
      eLpNorm (actualWeightedFullModelField hκ0 hκ1 p f s) 2 (volume.restrict (cylinderShell a b))≤
        C*ENNReal.ofReal ‖f‖ := by
  let J:=∫t in Icc a b,Real.exp (-6*t)
  have hJ:0≤J:=integral_nonneg (fun _=>(Real.exp_pos _).le)
  let D:=2/(((5/2:ℝ)^2-4)*(1-κ)^2)
  have hD:0≤D:=by dsimp only [D];positivity
  let N:=‖nativeSphereL2Inclusion‖
  have hN:0≤N:=norm_nonneg nativeSphereL2Inclusion
  let B:=(D+2)*N
  have hB:0≤B:=by dsimp only [B];positivity
  refine ⟨ENNReal.ofReal (Real.sqrt J*B),ENNReal.ofReal_ne_top,?_⟩
  intro p f s
  let v:ℝ→ℝ:=fun t=>p.orbit (t+p.phase)
  have hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
  have hb:∀t,0≤v t ∧ v t≤1:=fun t=>p.bounded (t+p.phase)
  let F:=halfEndFullSourceAngularCLM f
  let c:=nativeLowSolvedCurve v hv hb F
  let G:=nativeLowSourceCylinder c
  let U:ℝ→AngularL2:=nativeHalfHighDirichletPhysical hκ0 hκ1 p.potential p.kernel_bound
    p.potential_nonneg (halfEndH2SourceToAngularCLM f)
  let Z:ℝ→AngularL2:=fun t=>Real.exp (-2*t) • nativeLowProjection (c t)
  let w:=fullModelHighJoint hκ0 hκ1 p f
  let q:ℝ × S→ℝ:=fun y=>Real.exp (-2*y.1)*G y
  have hU:Continuous U:=nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 p.potential
    p.kernel_bound p.potential_nonneg _
  have hZ:Continuous Z:=(show Continuous (fun t:ℝ=>Real.exp (-2*t)) by fun_prop).smul
    (nativeLowProjection.continuous.comp c.continuous)
  have hw:Measurable w:=nativeHalfHighDirichletJoint_measurable hκ0 hκ1 p.potential
    p.kernel_bound p.potential_nonneg _
  have hq:Measurable q:=(measurable_const.mul measurable_fst).exp.mul G.continuous.measurable
  have hwa:∀t,(fun θ=>w (t,θ)) =ᵐ[angularVolume] (U t:S→ℝ):=
    nativeHalfHighDirichletJoint_ae hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg _
  have hqa (t:ℝ):(fun θ=>q (t,θ)) =ᵐ[angularVolume] (Z t:S→ℝ):=by
    have hs:=(ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_smul (Real.exp (-2*t)) (nativeLowProjection (c t)))
    filter_upwards [nativeLowSourceCylinder_ae c t,hs] with θ hθ hsm
    change Real.exp (-2*t)*G (t,θ)=_
    rw [hθ]
    simpa only [Pi.smul_apply,smul_eq_mul] using (hsm (mem_univ θ)).symm
  have hsumAE (t:ℝ):(fun θ=>w (t,θ)+q (t,θ)) =ᵐ[angularVolume] ((U t+Z t:AngularL2):S→ℝ):=by
    have ha:=(ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_add (U t) (Z t))
    filter_upwards [hwa t,hqa t,ha] with θ hh hl ha
    rw [hh,hl]
    simpa only [Pi.add_apply] using (ha (mem_univ θ)).symm
  have hUb (t:ℝ):‖U t‖≤Real.exp (-2*t)*(D*N*‖f‖):=by
    have hh:=nativeHalfHighDirichletPhysical_norm_le hκ0 hκ1 p.potential p.kernel_bound
      p.potential_nonneg (halfEndH2SourceToAngularCLM f) t
    calc
      _ ≤ Real.exp (-2*t)*D*‖halfEndH2SourceToAngularCLM f‖:=by simpa only [U,D,mul_assoc] using hh
      _ ≤ Real.exp (-2*t)*D*(N*‖f‖):=
        mul_le_mul_of_nonneg_left (halfEndH2SourceToAngularCLM_norm_le f) (by positivity)
      _ = _:=by ring
  have hZb (t:ℝ):‖Z t‖≤Real.exp (-2*t)*(2*N*‖f‖):=by
    rw [show Z t=Real.exp (-2*t) • nativeLowProjection (c t) from rfl,
      norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hc:‖nativeLowProjection (c t)‖≤2*‖F‖:=
      (nativeAngularProjection_apply_norm_le _ _).trans
        ((c.norm_coe_le_norm t).trans (nativeLowSolvedCurve_norm_le v hv hb F))
    exact hc.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (halfEndFullSourceAngular_norm_le f) (by norm_num : (0:ℝ)≤2))
  have hsb (t:ℝ):‖U t+Z t‖≤Real.exp (-2*t)*(B*‖f‖):=
    (norm_add_le _ _).trans ((add_le_add (hUb t) (hZb t)).trans_eq (by dsimp only [B];ring))
  have he:cylinderLift (fun y=>w y+q y)=fullModelPhysicalField hκ0 hκ1 p f:=by
    have hl:fullModelLowField p f=cylinderLift q:=nativeLowPhysicalField_eq_weighted_lift v hv hb F
    funext x
    change cylinderLift (fun y=>w y+q y) x=cylinderLift w x+fullModelLowField p f x
    rw [hl]
    by_cases hx:x=0
    · subst x;simp only [cylinderLift_zero,add_zero]
    · let y:puncturedSpace:=⟨x,hx⟩
      change cylinderLift (fun z=>w z+q z) (y:E)=cylinderLift w (y:E)+cylinderLift q (y:E)
      simp only [cylinderLift_coe,puncturedCylinderLift,mul_add]
  have hh:=weighted_lift_shell_square_bound (hU.add hZ) (hw.add hq) hsumAE (B*‖f‖) hsb s a b
  change cylinderLift (w+q)=fullModelPhysicalField hκ0 hκ1 p f at he
  rw [he] at hh
  refine ⟨hh.1,?_⟩
  have hn:=Poincare.Analysis.Sobolev.eLpNorm_two_le_sqrt_of_integral_sq_le hh.1 hh.2
  have hs:Real.sqrt (J*(B*‖f‖)^2)=(Real.sqrt J*B)*‖f‖:=by
    rw [Real.sqrt_mul hJ,Real.sqrt_sq (mul_nonneg hB (norm_nonneg f))]
    ring
  change _≤ENNReal.ofReal (Real.sqrt (J*(B*‖f‖)^2)) at hn
  rw [hs,ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) hB)] at hn
  exact hn

#print axioms exists_full_weighted_shell_L2_bound
end Yamabe3.Analysis.UniformElliptic
