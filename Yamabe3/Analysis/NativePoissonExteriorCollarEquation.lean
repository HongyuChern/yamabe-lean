import Yamabe3.Analysis.NativeCollarPotentialMultiplier
import Yamabe3.Analysis.NativePoissonExteriorInfiniteH2Collar
import Yamabe3.Analysis.L2MeasureRestriction

/-! The actual reversed-time exterior H2 field solves its homogeneous
physical equation on the exterior half of the entrance collar. The
artificial extension on the other side is not treated as a solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativePoissonExteriorPotential (P : NativeHighPotential) : ℝ →ᵇ ℝ :=
  P.potential.compContinuous ⟨Neg.neg,continuous_neg⟩

def nativeNegativeEntranceCollar : Set E := nativePoissonEntranceCollar ∩ {x | (1:ℝ)<‖x‖}

theorem nativeNegativeEntranceCollar_open : IsOpen nativeNegativeEntranceCollar :=
  (nativePolarTimeWindow_open (1/2)).inter (isOpen_lt continuous_const continuous_norm)

def nativeNegativeCollarRestrictionCLM :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) →L[ℝ] Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar) :=
  l2MeasureRestrictCLM (Measure.restrict_mono inter_subset_left le_rfl)

theorem nativeNegativeCollarRestrictionCLM_ae (F : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar)) :
    (nativeNegativeCollarRestrictionCLM F : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar] (F : E → ℝ) :=
  l2MeasureRestrict_ae (Measure.restrict_mono inter_subset_left le_rfl) F

theorem nativePoissonExteriorExtension_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (i : AngularIndex) (t : ℝ) (ht : t≤0) :
    finiteTimeLaplacian (nativePoissonExteriorExtension P b) i t=
      -(nativePoissonExteriorPotential P) t*nativePoissonExteriorExtension P b i t := by
  have h := P.exteriorExtension_jets b i t ht
  unfold finiteTimeLaplacian
  change _= -P.potential (-t)*nativePoissonExteriorExtension P b i t
  rw [h.2.2,h.1]
  by_cases hi : 6≤angularEigenvalue i
  · rw [nativeAngularRate_sq,max_eq_right hi]
    ring
  · have hz := congrFun (P.coordinate_low_zero b i (lt_of_not_ge hi)) (-t)
    rw [hz]
    ring

theorem nativePoissonExteriorFiniteCollar_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) {x : E} (hx : x∈nativeNegativeEntranceCollar) :
    nativeCoordinateLaplacian (nativePoissonExteriorFiniteCollar P b s) x+
      nativeHalfEndPotentialCoefficient (nativePoissonExteriorPotential P) x*nativePoissonExteriorFiniteCollar P b s x=0 := by
  have hx0 := cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx.1)
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx0
  have ht : -Real.log ‖x‖≤0 := neg_nonpos.mpr (Real.log_nonneg hx.2.le)
  let y : puncturedSpace := ⟨x,by change x≠0;exact hx0⟩
  change nativeCoordinateLaplacian (finitePhysical s (nativePoissonExteriorExtension P b)) x+
    nativeHalfEndPotentialCoefficient (nativePoissonExteriorPotential P) x*finitePhysical s (nativePoissonExteriorExtension P b) x=0
  rw [native_finitePhysical_laplacian s _ (fun i _ => P.exteriorExtension_C2 b i) hx0,finitePhysical_eq_lift]
  change cylinderLift (finiteAngular s (finiteTimeLaplacian (nativePoissonExteriorExtension P b))) (y:E)/‖x‖^2+
    nativeHalfEndPotentialCoefficient (nativePoissonExteriorPotential P) x*cylinderLift (finiteAngular s (nativePoissonExteriorExtension P b)) (y:E)=0
  rw [cylinderLift_coe,cylinderLift_coe]
  change radialScale ‖x‖*(∑ i ∈ s,finiteTimeLaplacian (nativePoissonExteriorExtension P b) i (-Real.log ‖x‖)*
    angularRepresentative i (cylinderCoordinates y).2)/‖x‖^2+
    ((nativePoissonExteriorPotential P) (-Real.log ‖x‖)/‖x‖^2)*(radialScale ‖x‖*(∑ i ∈ s,nativePoissonExteriorExtension P b i (-Real.log ‖x‖)*
      angularRepresentative i (cylinderCoordinates y).2))=0
  simp_rw [nativePoissonExteriorExtension_homogeneous P b _ _ ht,mul_assoc]
  rw [←Finset.mul_sum]
  ring

theorem nativePoissonExteriorCollarMode_homogeneous (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    nativeNegativeCollarRestrictionCLM ((∑ j : Fin 3,nativePoissonExteriorCollarSecondMode P b j j i)+
      nativeCollarPotentialMulCLM (nativePoissonExteriorPotential P) (nativePoissonExteriorCollarValueMode P b i))=0 := by
  let D := ∑ j : Fin 3,nativePoissonExteriorCollarSecondMode P b j j i
  let U := nativePoissonExteriorCollarValueMode P b i
  have hval : (U : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] nativePoissonExteriorCollarMode P b i :=
    (nativePoissonExteriorCollarMode_memLp P b i).1.coeFn_toLp
  have hsec : ∀ᵐ x ∂volume.restrict nativePoissonEntranceCollar,∀ j : Fin 3,
      nativePoissonExteriorCollarSecondMode P b j j i x=nativeCoordinateSecond j j (nativePoissonExteriorCollarMode P b i) x := by
    apply (ae_all_iff).mpr
    intro j
    exact ((nativePoissonExteriorCollarMode_memLp P b i).2.2 j j).coeFn_toLp
  have hD : (D : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] nativeCoordinateLaplacian (nativePoissonExteriorCollarMode P b i) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => nativePoissonExteriorCollarSecondMode P b j j i),hsec] with x hsum hsec
    change D x=_
    rw [hsum]
    simp only [Finset.sum_apply]
    change (∑ j : Fin 3,nativePoissonExteriorCollarSecondMode P b j j i x)=
      ∑ j : Fin 3,nativeCoordinateSecond j j (nativePoissonExteriorCollarMode P b i) x
    simp_rw [hsec]
  have hres : (⇑(D+nativeCollarPotentialMulCLM (nativePoissonExteriorPotential P) U))=ᵐ[volume.restrict nativeNegativeEntranceCollar] (fun _ => 0) := by
    have hm : volume.restrict nativeNegativeEntranceCollar≤volume.restrict nativePoissonEntranceCollar :=
      Measure.restrict_mono inter_subset_left le_rfl
    filter_upwards [ae_mono hm hval,ae_mono hm hD,ae_mono hm (nativeCollarPotentialMulCLM_ae (nativePoissonExteriorPotential P) U),
      ae_mono hm (Lp.coeFn_add D (nativeCollarPotentialMulCLM (nativePoissonExteriorPotential P) U)),
      ae_restrict_mem nativeNegativeEntranceCollar_open.measurableSet] with x hu hd hq ha hx
    rw [ha]
    simp only [Pi.add_apply]
    rw [hd,hq,hu]
    exact nativePoissonExteriorFiniteCollar_homogeneous P b {i} hx
  apply Lp.ext
  exact (nativeNegativeCollarRestrictionCLM_ae _).trans (hres.trans (Lp.coeFn_zero ℝ 2 _).symm)

theorem nativePoissonExteriorCollar_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativeNegativeCollarRestrictionCLM ((∑ j : Fin 3,nativePoissonExteriorCollarSecond P b j j)+
      nativeCollarPotentialMulCLM (nativePoissonExteriorPotential P) (nativePoissonExteriorCollarValue P b))=0 := by
  have hs := nativePoissonExteriorCollar_modes_summable P b hb
  have hd : Summable (fun i => ∑ j : Fin 3,nativePoissonExteriorCollarSecondMode P b j j i) :=
    (hasSum_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) => (hs.2.2 j j).hasSum)).summable
  have he := Summable.tsum_finsetSum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) => hs.2.2 j j)
  change nativeNegativeCollarRestrictionCLM ((∑ j : Fin 3,∑' i,nativePoissonExteriorCollarSecondMode P b j j i)+
    nativeCollarPotentialMulCLM (nativePoissonExteriorPotential P) (∑' i,nativePoissonExteriorCollarValueMode P b i))=0
  rw [←he,(nativeCollarPotentialMulCLM (nativePoissonExteriorPotential P)).map_tsum hs.1,
    ←Summable.tsum_add hd ((nativeCollarPotentialMulCLM (nativePoissonExteriorPotential P)).summable hs.1),
    nativeNegativeCollarRestrictionCLM.map_tsum (hd.add ((nativeCollarPotentialMulCLM (nativePoissonExteriorPotential P)).summable hs.1))]
  simp_rw [nativePoissonExteriorCollarMode_homogeneous]
  exact tsum_zero

#print axioms nativePoissonExteriorExtension_homogeneous
#print axioms nativePoissonExteriorFiniteCollar_homogeneous
#print axioms nativePoissonExteriorCollarMode_homogeneous
#print axioms nativePoissonExteriorCollar_homogeneous
end Yamabe3.Analysis.SpherePolar
