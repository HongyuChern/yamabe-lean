import Yamabe3.Analysis.NativeCollarPotentialMultiplier
import Yamabe3.Analysis.NativePoissonInfiniteH2Collar
import Yamabe3.Analysis.L2MeasureRestriction

/-! The original Poisson field satisfies the homogeneous physical
Laplacian equation on the positive-time part of the actual entrance collar.
The negative-time reflection is not treated as a homogeneous solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativePositiveEntranceCollar : Set E := nativePoissonEntranceCollar ∩ Metric.ball 0 1

theorem nativePositiveEntranceCollar_open : IsOpen nativePositiveEntranceCollar :=
  (nativePolarTimeWindow_open (1/2)).inter Metric.isOpen_ball

def nativePositiveCollarRestrictionCLM :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) →L[ℝ] Lp ℝ 2 (volume.restrict nativePositiveEntranceCollar) :=
  l2MeasureRestrictCLM (Measure.restrict_mono inter_subset_left le_rfl)

theorem nativePositiveCollarRestrictionCLM_ae (F : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar)) :
    (nativePositiveCollarRestrictionCLM F : E → ℝ)=ᵐ[volume.restrict nativePositiveEntranceCollar] (F : E → ℝ) :=
  l2MeasureRestrict_ae (Measure.restrict_mono inter_subset_left le_rfl) F

theorem nativePoissonEntranceExtension_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (i : AngularIndex) (t : ℝ) (ht : 0≤t) :
    finiteTimeLaplacian (nativePoissonEntranceExtension P b) i t=
      -P.potential t*nativePoissonEntranceExtension P b i t := by
  have h := P.entranceExtension_jets b i t ht
  unfold finiteTimeLaplacian
  rw [h.2.2,h.1]
  by_cases hi : 6≤angularEigenvalue i
  · rw [nativeAngularRate_sq,max_eq_right hi]
    ring
  · have hz := congrFun (P.coordinate_low_zero b i (lt_of_not_ge hi)) t
    rw [hz]
    ring

theorem nativePoissonFiniteCollar_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) {x : E} (hx : x∈nativePositiveEntranceCollar) :
    nativeCoordinateLaplacian (nativePoissonFiniteCollar P b s) x+
      nativeHalfEndPotentialCoefficient P.potential x*nativePoissonFiniteCollar P b s x=0 := by
  have hx0 := cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx.1)
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx0
  have ht : 0≤-Real.log ‖x‖ := by
    have hr : ‖x‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hx.2
    have hlog := Real.log_nonpos hn.le hr.le
    linarith
  let y : puncturedSpace := ⟨x,by change x≠0;exact hx0⟩
  change nativeCoordinateLaplacian (finitePhysical s (nativePoissonEntranceExtension P b)) x+
    nativeHalfEndPotentialCoefficient P.potential x*finitePhysical s (nativePoissonEntranceExtension P b) x=0
  rw [native_finitePhysical_laplacian s _ (fun i _ => P.entranceExtension_C2 b i) hx0,finitePhysical_eq_lift]
  change cylinderLift (finiteAngular s (finiteTimeLaplacian (nativePoissonEntranceExtension P b))) (y:E)/‖x‖^2+
    nativeHalfEndPotentialCoefficient P.potential x*cylinderLift (finiteAngular s (nativePoissonEntranceExtension P b)) (y:E)=0
  rw [cylinderLift_coe,cylinderLift_coe]
  change radialScale ‖x‖*(∑ i ∈ s,finiteTimeLaplacian (nativePoissonEntranceExtension P b) i (-Real.log ‖x‖)*
    angularRepresentative i (cylinderCoordinates y).2)/‖x‖^2+
    (P.potential (-Real.log ‖x‖)/‖x‖^2)*(radialScale ‖x‖*(∑ i ∈ s,nativePoissonEntranceExtension P b i (-Real.log ‖x‖)*
      angularRepresentative i (cylinderCoordinates y).2))=0
  simp_rw [nativePoissonEntranceExtension_homogeneous P b _ _ ht,mul_assoc]
  rw [←Finset.mul_sum]
  ring

theorem nativePoissonCollarMode_homogeneous (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    nativePositiveCollarRestrictionCLM ((∑ j : Fin 3,nativePoissonCollarSecondMode P b j j i)+
      nativeCollarPotentialMulCLM P.potential (nativePoissonCollarValueMode P b i))=0 := by
  let D := ∑ j : Fin 3,nativePoissonCollarSecondMode P b j j i
  let U := nativePoissonCollarValueMode P b i
  have hval : (U : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] nativePoissonCollarMode P b i :=
    (nativePoissonCollarMode_memLp P b i).1.coeFn_toLp
  have hsec : ∀ᵐ x ∂volume.restrict nativePoissonEntranceCollar,∀ j : Fin 3,
      nativePoissonCollarSecondMode P b j j i x=nativeCoordinateSecond j j (nativePoissonCollarMode P b i) x := by
    apply (ae_all_iff).mpr
    intro j
    exact ((nativePoissonCollarMode_memLp P b i).2.2 j j).coeFn_toLp
  have hD : (D : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] nativeCoordinateLaplacian (nativePoissonCollarMode P b i) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => nativePoissonCollarSecondMode P b j j i),hsec] with x hsum hsec
    change D x=_
    rw [hsum]
    simp only [Finset.sum_apply]
    change (∑ j : Fin 3,nativePoissonCollarSecondMode P b j j i x)=
      ∑ j : Fin 3,nativeCoordinateSecond j j (nativePoissonCollarMode P b i) x
    simp_rw [hsec]
  have hres : (⇑(D+nativeCollarPotentialMulCLM P.potential U))=ᵐ[volume.restrict nativePositiveEntranceCollar] (fun _ => 0) := by
    have hm : volume.restrict nativePositiveEntranceCollar≤volume.restrict nativePoissonEntranceCollar :=
      Measure.restrict_mono inter_subset_left le_rfl
    filter_upwards [ae_mono hm hval,ae_mono hm hD,ae_mono hm (nativeCollarPotentialMulCLM_ae P.potential U),
      ae_mono hm (Lp.coeFn_add D (nativeCollarPotentialMulCLM P.potential U)),
      ae_restrict_mem nativePositiveEntranceCollar_open.measurableSet] with x hu hd hq ha hx
    rw [ha]
    simp only [Pi.add_apply]
    rw [hd,hq,hu]
    exact nativePoissonFiniteCollar_homogeneous P b {i} hx
  apply Lp.ext
  exact (nativePositiveCollarRestrictionCLM_ae _).trans (hres.trans (Lp.coeFn_zero ℝ 2 _).symm)

theorem nativePoissonCollar_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativePositiveCollarRestrictionCLM ((∑ j : Fin 3,nativePoissonCollarSecond P b j j)+
      nativeCollarPotentialMulCLM P.potential (nativePoissonCollarValue P b))=0 := by
  have hs := nativePoissonCollar_modes_summable P b hb
  have hd : Summable (fun i => ∑ j : Fin 3,nativePoissonCollarSecondMode P b j j i) :=
    (hasSum_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) => (hs.2.2 j j).hasSum)).summable
  have he := Summable.tsum_finsetSum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) => hs.2.2 j j)
  change nativePositiveCollarRestrictionCLM ((∑ j : Fin 3,∑' i,nativePoissonCollarSecondMode P b j j i)+
    nativeCollarPotentialMulCLM P.potential (∑' i,nativePoissonCollarValueMode P b i))=0
  rw [←he,(nativeCollarPotentialMulCLM P.potential).map_tsum hs.1,
    ←Summable.tsum_add hd ((nativeCollarPotentialMulCLM P.potential).summable hs.1),
    nativePositiveCollarRestrictionCLM.map_tsum (hd.add ((nativeCollarPotentialMulCLM P.potential).summable hs.1))]
  simp_rw [nativePoissonCollarMode_homogeneous]
  exact tsum_zero

#print axioms nativePoissonEntranceExtension_homogeneous
#print axioms nativePoissonFiniteCollar_homogeneous
#print axioms nativePoissonCollarMode_homogeneous
#print axioms nativePoissonCollar_homogeneous
end Yamabe3.Analysis.SpherePolar
