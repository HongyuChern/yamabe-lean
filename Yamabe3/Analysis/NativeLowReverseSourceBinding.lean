import Yamabe3.Analysis.NativeLowReverseL2PhysicalEquation

/-! Source preprocessing for the reversed low producer. A bounded time
weight agrees with exp(-4t) on the actual collar. Reflection and the
inverse-fourth physical factor then cancel exactly on that collar.
No extra integrability assumption is imposed on the given L2 source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeReverseSourceWeight : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => Real.exp (-4*max (-1) (min 1 t)))
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.max (continuous_const.min continuous_id))))
    (Real.exp 4) (fun t => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_le_exp]
      nlinarith [le_max_left (-1:ℝ) (min 1 t)])

theorem nativeReverseSourceWeight_eq (t : ℝ) (ht : t∈Icc (-1:ℝ) 1) :
    nativeReverseSourceWeight t=Real.exp (-4*t) := by
  change Real.exp (-4*max (-1) (min 1 t))=_
  rw [min_eq_right ht.2,max_eq_right ht.1]

def nativeLowReverseSourcePrepareCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  (l2TimeReflectCLM AngularSpectralSpace).comp (spectralL2PotentialMulCLM nativeReverseSourceWeight)

theorem nativeLowL2PhysicalSource_weight_ae (W : ℝ →ᵇ ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    (nativeL2LowPhysicalSourceCLM (spectralL2PotentialMulCLM W F) : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => W (-Real.log ‖x‖)*(nativeL2LowPhysicalSourceCLM F : E→ℝ) x) := by
  let A := nativeL2LowAngularCLM F
  let w := nativeAngularL2Joint A
  have hw := nativeAngularL2Joint_measurable A
  have hwF : ∀ᵐt : ℝ ∂volume,(fun θ => w (t,θ))=ᵐ[angularVolume]
      (nativeLowProjection (angularBasis.repr.symm (F t)) : S→ℝ) := by
    filter_upwards [nativeL2LowAngularCLM_ae F] with t ht
    have h := nativeAngularL2Joint_ae A t
    change A t=_ at ht
    rw [ht] at h
    exact h
  have hq := nativeL2LowPhysicalSource_eq_lift (spectralL2PotentialMulCLM W F)
    ((W.continuous.measurable.comp measurable_fst).mul hw) (by
      filter_upwards [spectralL2PotentialMul_coe_ae W F,hwF] with t ht hw
      change spectralL2PotentialMulCLM W F t=W t • F t at ht
      rw [ht,map_smul,map_smul]
      have hs := (ae_restrict_iff' MeasurableSet.univ).mp
        (Lp.coeFn_smul (W t) (nativeLowProjection (angularBasis.repr.symm (F t))))
      filter_upwards [hw,hs] with θ hθ hs
      change W t*w (t,θ)=_
      rw [hθ]
      simpa only [Pi.smul_apply,smul_eq_mul] using (hs (mem_univ θ)).symm)
  have hf := nativeL2LowPhysicalSource_eq_lift F hw hwF
  filter_upwards [hq,hf,ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hq hf hx
  rw [hq,hf]
  have hx0 := cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx)
  let y : puncturedSpace := ⟨x,by change x≠0;exact hx0⟩
  change cylinderLift (fun p => W p.1*w p) (y:E)=W (-Real.log ‖x‖)*cylinderLift w (y:E)
  rw [cylinderLift_coe,cylinderLift_coe]
  change radialScale ‖x‖*(W (-Real.log ‖x‖)*w (cylinderCoordinates y))=
    W (-Real.log ‖x‖)*(radialScale ‖x‖*w (cylinderCoordinates y))
  ring

theorem nativeReverseSourceWeight_physical {x : E} (hx : x∈nativePoissonEntranceCollar) :
    nativeReverseSourceWeight (-Real.log ‖x‖)=‖x‖^4 := by
  have hx0 := cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx)
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx0
  have ht : -Real.log ‖x‖∈Icc (-1:ℝ) 1 := by
    rcases hx with ⟨hx0,ht⟩
    change -(1/2:ℝ) < -Real.log ‖x‖ ∧ -Real.log ‖x‖<1/2 at ht
    constructor <;> linarith [ht.1,ht.2]
  rw [nativeReverseSourceWeight_eq _ ht]
  calc
    _=Real.exp (Real.log ‖x‖+Real.log ‖x‖+Real.log ‖x‖+Real.log ‖x‖) := by congr 1;ring
    _=_ := by simp only [Real.exp_add,Real.exp_log hn];ring

theorem nativeLowReverseSourcePrepare_reconstructs (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowReverseL2SourceCLM (nativeLowReverseSourcePrepareCLM F)=nativeL2LowPhysicalSourceCLM F := by
  change nativeInverseFourthPowerCollarCLM
    (nativeL2LowPhysicalSourceCLM (l2TimeReflectCLM AngularSpectralSpace
      (l2TimeReflectCLM AngularSpectralSpace (spectralL2PotentialMulCLM nativeReverseSourceWeight F))))=_
  rw [l2TimeReflect_involution]
  apply Lp.ext
  filter_upwards [nativeCollarLocalMulCLM_ae (fun x => (‖x‖^4)⁻¹) nativeInverseFourthPower_continuousOn
    (nativeL2LowPhysicalSourceCLM (spectralL2PotentialMulCLM nativeReverseSourceWeight F)),
    nativeLowL2PhysicalSource_weight_ae nativeReverseSourceWeight F,
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hm hw hx
  change nativeCollarLocalMulCLM (fun x => (‖x‖^4)⁻¹) nativeInverseFourthPower_continuousOn
    (nativeL2LowPhysicalSourceCLM (spectralL2PotentialMulCLM nativeReverseSourceWeight F)) x=_
  rw [hm,hw,nativeReverseSourceWeight_physical hx]
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx))
  rw [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero 4 hn),one_mul]

#print axioms nativeReverseSourceWeight_eq
#print axioms nativeLowL2PhysicalSource_weight_ae
#print axioms nativeReverseSourceWeight_physical
#print axioms nativeLowReverseSourcePrepare_reconstructs
end Yamabe3.Analysis.SpherePolar
