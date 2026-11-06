import Yamabe3.Analysis.NativeBubbleLowCollarEquation

/-! The real exterior model Jacobian on strong H2 jets. Its compensating
source is an actual L2 class identified with the previously constructed
physical source, while the high exterior field contributes zero. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeExteriorModelJacobianCLM (V : ℝ →ᵇ ℝ) :
    NativeCollarJet →L[ℝ] Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar) :=
  (-8:ℝ) • nativeNegativeCollarRestrictionCLM.comp
    ((∑j : Fin 3,nativeCollarJetSecondCLM j j)+(nativeCollarPotentialMulCLM V).comp nativeCollarJetValueCLM)

theorem nativeExteriorModelJacobianCLM_apply (V : ℝ →ᵇ ℝ) (J : NativeCollarJet) :
    nativeExteriorModelJacobianCLM V J=
      (-8:ℝ) • nativeNegativeCollarRestrictionCLM
        ((∑j : Fin 3,J.2.2 j j)+nativeCollarPotentialMulCLM V J.1) := by
  simp [nativeExteriorModelJacobianCLM,nativeCollarJetSecondCLM,nativeCollarJetValueCLM]

theorem nativeExteriorModelJacobian_C2_ae (V : ℝ →ᵇ ℝ) (u : nativeC2OffZero) :
    (nativeExteriorModelJacobianCLM V (nativeC2CollarJetLinear u) : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => -8*nativeCoordinateLaplacian u.val x-8*nativeHalfEndPotentialCoefficient V x*u.val x) := by
  let J := nativeC2CollarJetLinear u
  let D := ∑j : Fin 3,J.2.2 j j
  let Q := nativeCollarPotentialMulCLM V J.1
  have hval : (J.1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u.val :=
    (nativeC2Collar_memLp u.property).1.coeFn_toLp
  have hsec : ∀ᵐx∂volume.restrict nativePoissonEntranceCollar,∀j : Fin 3,
      (J.2.2 j j : E → ℝ) x=nativeCoordinateSecond j j u.val x := by
    apply eventually_all.mpr
    intro j
    exact ((nativeC2Collar_memLp u.property).2.2 j j).coeFn_toLp
  have hsum : (D : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] nativeCoordinateLaplacian u.val := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => J.2.2 j j),hsec] with x hs hh
    change D x=_
    rw [hs]
    simp only [Finset.sum_apply,hh,nativeCoordinateLaplacian,nativeCoordinateSecond]
    rfl
  have hm : volume.restrict nativeNegativeEntranceCollar≤volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono inter_subset_left le_rfl
  rw [nativeExteriorModelJacobianCLM_apply]
  filter_upwards [Lp.coeFn_smul (-8:ℝ) (nativeNegativeCollarRestrictionCLM (D+Q)),
    nativeNegativeCollarRestrictionCLM_ae (D+Q),ae_mono hm (Lp.coeFn_add D Q),ae_mono hm hsum,
    ae_mono hm hval,ae_mono hm (nativeCollarPotentialMulCLM_ae V J.1)] with x hc hr ha hd hu hq
  change ((-8:ℝ) • nativeNegativeCollarRestrictionCLM (D+Q)) x=_
  change Q x=nativeHalfEndPotentialCoefficient V x*J.1 x at hq
  rw [hc]
  simp only [Pi.smul_apply,smul_eq_mul,hr,ha,Pi.add_apply,hd,hq,hu]
  ring

theorem nativeExteriorModelJacobian_high_zero (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential P)
      (nativePoissonExteriorCollarJet P b hb).val=0 := by
  rw [nativeExteriorModelJacobianCLM_apply]
  change (-8:ℝ) • nativeNegativeCollarRestrictionCLM
    ((∑j : Fin 3,nativePoissonExteriorCollarSecond P b j j)+
      nativeCollarPotentialMulCLM (nativePoissonExteriorPotential P) (nativePoissonExteriorCollarValue P b))=0
  rw [nativePoissonExteriorCollar_homogeneous P b hb,smul_zero]

theorem nativeBubbleLowCollar_source_ae (t₀ : ℝ) (c : AngularIndex → ℝ)
    (q : AngularIndex → ℝ → ℝ)
    (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i))
    (heq : ∀i∈nativeLowIndexFinset,∀t,deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t=
      -c i*bubbleCompensation i t) :
    (nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
      (nativeBubbleLowCollarJet t₀ q hq).val : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      nativeBubbleCollarCompensation t₀ c := by
  have h := nativeExteriorModelJacobian_C2_ae
    (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
    ⟨finitePhysical nativeLowIndexFinset (fun i t => q i (t₀+t)),
      finitePhysical_contDiffOn_offZero_C2 _ _ (fun i hi => (hq i hi).comp (contDiff_const.add contDiff_id))⟩
  filter_upwards [h,ae_restrict_mem nativeNegativeEntranceCollar_open.measurableSet] with x hh hx
  change nativeExteriorModelJacobianCLM _ (nativeC2CollarJetLinear _) x=_
  rw [hh]
  exact nativeBubbleLowCollar_physical_equation t₀ c q hq heq
    (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx.1))

theorem nativeBubbleHighLowCollar_same_source (t₀ : ℝ) (c : AngularIndex → ℝ)
    (q : AngularIndex → ℝ → ℝ)
    (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i))
    (heq : ∀i∈nativeLowIndexFinset,∀t,deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t=
      -c i*bubbleCompensation i t) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    let B := fullBubbleHighPotential (-t₀)
    let K := nativeBubbleLowCollarJet t₀ q hq+nativePoissonExteriorCollarJet B b hb
    (nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential B) K.val : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      nativeBubbleCollarCompensation t₀ c := by
  dsimp only
  rw [Submodule.coe_add,map_add,nativeExteriorModelJacobian_high_zero,add_zero]
  exact nativeBubbleLowCollar_source_ae t₀ c q hq heq

#print axioms nativeExteriorModelJacobian_C2_ae
#print axioms nativeExteriorModelJacobian_high_zero
#print axioms nativeBubbleLowCollar_source_ae
#print axioms nativeBubbleHighLowCollar_same_source
end Yamabe3.Analysis.SpherePolar
