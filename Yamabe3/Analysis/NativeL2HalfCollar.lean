import Yamabe3.Analysis.NativeL2ParticularAllSourceIdentity
import Yamabe3.Analysis.NativeL2EntranceH1CLM
import Yamabe3.Analysis.NativePoissonCollarIdentification
import Yamabe3.Analysis.NativePoissonCollarNormBound

/-! The same L2-source high field with its actual entrance removed by
the original same-potential Poisson operator. Its physical collar has one
value and genuine first/second weak jets. The negative-time extension is
only a collar extension, not a negative-time homogeneous PDE claim. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

def nativeL2HalfEntrance (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) : AngularH1 :=
  nativeL2EntranceH1 P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F

def nativeL2HalfCollarCurve (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (t : ℝ) : AngularL2 :=
  nativeConjugatedCurve (nativeL2ParticularAngularCLM P.potential F) t-
    nativePoissonReflectedCurve P (nativeL2HalfEntrance P hplus F) t

def nativeL2HalfCollarValue (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F-
    nativePoissonCollarValue P (nativeL2HalfEntrance P hplus F)
def nativeL2HalfCollarFirst (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2ParticularFirstCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus j F-
    nativePoissonCollarFirst P (nativeL2HalfEntrance P hplus F) j
def nativeL2HalfCollarSecond (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (k j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus k j F-
    nativePoissonCollarSecond P (nativeL2HalfEntrance P hplus F) k j

theorem nativeL2HalfCollarCurve_continuous (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    Continuous (nativeL2HalfCollarCurve P hplus F) :=
  (nativeConjugatedCurve_continuous _).sub (nativePoissonReflectedCurve_continuous P _)

theorem nativeL2HalfCollarCurve_zero (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfCollarCurve P hplus F 0=0 := by
  have he := (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F).1
  change angularEmbedding (nativeL2HalfEntrance P hplus F)=_ at he
  unfold nativeL2HalfCollarCurve nativePoissonReflectedCurve
  rw [if_pos le_rfl,NativeHighPotential.curve,nativeHalfHighPotentialPhysical_zero,
    nativeHighEnergyProjectionCLM_embedding,he]
  change Real.exp (-2*0) • nativeHighProjection (angularBasis.repr.symm
      (spectralL2PotentialContinuousCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
        (by norm_num : |(-2:ℝ)|<5/2) P.potential F 0))-
    nativeHighProjection (angularBasis.repr.symm
      (spectralL2PotentialContinuousCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
        (by norm_num : |(-2:ℝ)|<5/2) P.potential F 0))=0
  simp

theorem nativeL2HalfCollarCurve_positive (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ))
    (t : ℝ) (ht : 0≤t) :
    nativeL2HalfCollarCurve P hplus F t=
      nativeConjugatedCurve (nativeL2ParticularAngularCLM P.potential F) t-P.curve (nativeL2HalfEntrance P hplus F) t := by
  simp only [nativeL2HalfCollarCurve,nativePoissonReflectedCurve,if_pos ht]

theorem nativeL2HalfCollarValue_eq_lift
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2HalfCollarCurve P hplus F t : S → ℝ)) :
    (nativeL2HalfCollarValue P hplus F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
  let W := nativeL2ParticularAngularCLM P.potential F
  let v := nativeConjugatedJoint W
  have hv := nativeConjugatedJoint_measurable W
  have hva := nativeConjugatedJoint_ae W
  obtain ⟨z,hz,hza,_⟩ := nativePoissonReflectedCurve_joint_representative P (nativeL2HalfEntrance P hplus F)
  have hzv := nativePoissonCollarValue_eq_lift P _
    (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F).2.1 hz.measurable hza
  have hvv := nativeL2ParticularValueCLM_eq_lift P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F hv hva
  have hsame (t : ℝ) : (fun θ => v (t,θ)-z (t,θ))=ᵐ[angularVolume] (fun θ => w (t,θ)) := by
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_sub (nativeConjugatedCurve W t) (nativePoissonReflectedCurve P (nativeL2HalfEntrance P hplus F) t))
    filter_upwards [hva t,hza t,hae t,hc] with θ hv hz hw hc
    change v (t,θ)=_ at hv
    rw [hv,hz,hw]
    exact (hc (mem_univ θ)).symm
  have hrep := native_collar_lift_ae_eq_of_joint_slices (hv.sub hz.measurable) hw hsame
  change cylinderLift (fun p => v p-z p)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w at hrep
  rw [cylinderLift_sub] at hrep
  filter_upwards [hvv,hzv,hrep,Lp.coeFn_sub
    (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F)
    (nativePoissonCollarValue P (nativeL2HalfEntrance P hplus F))] with x hv hz hr hc
  change (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F-
    nativePoissonCollarValue P (nativeL2HalfEntrance P hplus F)) x=cylinderLift w x
  rw [hc]
  simp only [Pi.sub_apply]
  change nativePoissonCollarValue P (nativeL2HalfEntrance P hplus F) x=cylinderLift z x at hz
  rw [hv,hz]
  exact hr

private theorem weakLp_sub {Ω : Set E} {j : Fin 3} {u v du dv : Lp ℝ 2 (volume.restrict Ω)}
    (hu : HasWeakPartialDeriv j du u Ω) (hv : HasWeakPartialDeriv j dv v Ω) :
    HasWeakPartialDeriv j ⇑(du-dv) ⇑(u-v) Ω := by
  simpa only [neg_one_smul,←sub_eq_add_neg] using native_weakPartial_Lp_add hu (native_weakPartial_Lp_smul (-1) hv)

theorem nativeL2HalfCollar_H2_and_jets
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeL2HalfCollarValue P hplus F) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativeL2HalfCollarFirst P hplus F j)
        (nativeL2HalfCollarValue P hplus F) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativeL2HalfCollarSecond P hplus F k j)
        (nativeL2HalfCollarFirst P hplus F j) nativePoissonEntranceCollar) := by
  have h := nativeL2ParticularCLM_weak_jets P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F
  have hb := nativePoissonCollar_H2_and_strong_jets P (nativeL2HalfEntrance P hplus F)
    (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F).2.1
  have h1 (j : Fin 3) : HasWeakPartialDeriv j (nativeL2HalfCollarFirst P hplus F j)
      (nativeL2HalfCollarValue P hplus F) nativePoissonEntranceCollar := weakLp_sub (h.1 j) (hb.2.1 j)
  have h2 (k j : Fin 3) : HasWeakPartialDeriv k (nativeL2HalfCollarSecond P hplus F k j)
      (nativeL2HalfCollarFirst P hplus F j) nativePoissonEntranceCollar := weakLp_sub (h.2 k j) (hb.2.2.1 k j)
  refine ⟨?_,h1,h2⟩
  apply memWkp_succ_of_weakDerivatives (nativePolarTimeWindow_open (1/2)) (by norm_num : (1:ℝ≥0∞)≤2)
    (Lp.memLp _) (g := fun j => nativeL2HalfCollarFirst P hplus F j)
  · intro j
    apply MemWkp.one_iff_memW1p.mpr
    exact ⟨Lp.memLp _,fun k => ⟨_,Lp.memLp _,h2 k j⟩⟩
  · exact h1

theorem exists_nativeL2Half_same_field_H2_zero_entrance
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfCollarCurve P hplus F 0=0 ∧
    ∃ w : ℝ × S → ℝ,StronglyMeasurable w ∧
      (∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2HalfCollarCurve P hplus F t : S → ℝ)) ∧
      (nativeL2HalfCollarValue P hplus F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w ∧
      MemWkp 2 2 (nativeL2HalfCollarValue P hplus F) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativeL2HalfCollarFirst P hplus F j)
        (nativeL2HalfCollarValue P hplus F) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativeL2HalfCollarSecond P hplus F k j)
        (nativeL2HalfCollarFirst P hplus F j) nativePoissonEntranceCollar) := by
  obtain ⟨w,hw,hae⟩ := exists_joint_L2_representative_of_continuous (nativeL2HalfCollarCurve_continuous P hplus F)
  have hae' : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2HalfCollarCurve P hplus F t : S → ℝ) := by
    intro t
    simpa only [Measure.restrict_univ] using hae t
  exact ⟨nativeL2HalfCollarCurve_zero P hplus F,w,hw,hae',
    nativeL2HalfCollarValue_eq_lift P hplus F hw.measurable hae',nativeL2HalfCollar_H2_and_jets P hplus F⟩

#print axioms nativeL2HalfCollarCurve_zero
#print axioms nativeL2HalfCollarCurve_positive
#print axioms nativeL2HalfCollarValue_eq_lift
#print axioms nativeL2HalfCollar_H2_and_jets
#print axioms exists_nativeL2Half_same_field_H2_zero_entrance
end Yamabe3.Analysis.SpherePolar
