import Yamabe3.Analysis.NativeExteriorShiftedFinite
import Yamabe3.Analysis.NativeC2CollarSeriesNorm
import Yamabe3.Analysis.NativePoissonExteriorCurve
import Yamabe3.Analysis.NativeWeightedLift
import Yamabe3.Analysis.NativeCollarSeriesIdentification

/-! The same actual exterior Poisson curve has H2 jets on every scale.
The boundary three-halves energy and exact exp(4s) squared-norm cost are
retained. Thus the estimates are uniform on the exterior half-end s <= 0. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativeExteriorShiftedMode (P : NativeHighPotential) (s : ℝ) (b : AngularH1) (i : AngularIndex) : E → ℝ :=
  finitePhysical {i} (nativeExteriorShiftedCoefficient P b s)

theorem nativeExteriorShiftedMode_C2 (P : NativeHighPotential) (s : ℝ) (b : AngularH1) (i : AngularIndex) :
    ContDiffOn ℝ 2 (nativeExteriorShiftedMode P s b i) ({0}ᶜ : Set E) :=
  finitePhysical_contDiffOn_offZero_C2 {i} _ (fun j _ => nativeExteriorShiftedCoefficient_C2 P b s j)

theorem nativeExteriorShiftedMode_sum (P : NativeHighPotential) (s : ℝ) (b : AngularH1) (m : Finset AngularIndex) :
    (fun x => ∑ i ∈ m,nativeExteriorShiftedMode P s b i x)=finitePhysical m (nativeExteriorShiftedCoefficient P b s) := by
  funext x
  simp [nativeExteriorShiftedMode,finitePhysical]

 theorem nativeExteriorShiftedMode_budget (P : NativeHighPotential) (s : ℝ) 
    (b : AngularH1) (m : Finset AngularIndex) :
    ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),(∑ i ∈ m,nativeExteriorShiftedMode P s b i x)^2)+
      (∫ x in nativePolarTimeWindow (Ioo (-1) 1),
        nativeCoordinateLaplacian (fun y => ∑ i ∈ m,nativeExteriorShiftedMode P s b i y) x^2)) ≤
          (12000*Real.exp 2*Real.exp (4*s)*(4+P.derivativeBound))*
            (∑ i ∈ m,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  have h := (nativeExteriorShiftedFinite_energy P b s m).2.2.2
  simpa only [←nativeExteriorShiftedMode_sum P s b m] using h

def nativeExteriorShiftedValue (P : NativeHighPotential) (s : ℝ) (b : AngularH1) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarValue (nativeExteriorShiftedMode_C2 P s b i)
def nativeExteriorShiftedFirst (P : NativeHighPotential) (s : ℝ) (b : AngularH1) (j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarFirst (nativeExteriorShiftedMode_C2 P s b i) j
def nativeExteriorShiftedSecond (P : NativeHighPotential) (s : ℝ) (b : AngularH1) (k j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarSecond (nativeExteriorShiftedMode_C2 P s b i) k j

 theorem nativeExteriorShifted_summable (P : NativeHighPotential) (s : ℝ) 
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    Summable (fun i => nativeC2CollarValue (nativeExteriorShiftedMode_C2 P s b i)) ∧
      (∀ j,Summable (fun i => nativeC2CollarFirst (nativeExteriorShiftedMode_C2 P s b i) j)) ∧
      (∀ k j,Summable (fun i => nativeC2CollarSecond (nativeExteriorShiftedMode_C2 P s b i) k j)) := by
  have hd := P.derivativeBound_nonneg
  exact nativeC2Collar_series_summable _ _ hb (fun i => sq_nonneg _)
    (by positivity) (nativeExteriorShiftedMode_budget P s b)

 theorem nativeExteriorShifted_H2_same_jets (P : NativeHighPotential) (s : ℝ) 
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    MemWkp 2 2 (nativeExteriorShiftedValue P s b) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativeExteriorShiftedFirst P s b j) (nativeExteriorShiftedValue P s b) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativeExteriorShiftedSecond P s b k j) (nativeExteriorShiftedFirst P s b j) nativePoissonEntranceCollar) := by
  have hd := P.derivativeBound_nonneg
  exact nativeC2Collar_series_H2 _ _ hb (fun i => sq_nonneg _)
    (by positivity) (nativeExteriorShiftedMode_budget P s b)

 theorem exists_nativeExteriorShifted_H2_bounds (P : NativeHighPotential) :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0 ≤ C ∧ 0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (s : ℝ) (b : AngularH1),NativeAngularSpectralRegular (3/2) (angularEmbedding b) →
        ‖nativeExteriorShiftedValue P s b‖^2 ≤ (C*Real.exp (4*s))*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) ∧
        (∀ j,‖nativeExteriorShiftedFirst P s b j‖^2 ≤ (G*Real.exp (4*s))*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)) ∧
        (∀ k j,‖nativeExteriorShiftedSecond P s b k j‖^2 ≤ (K k*Real.exp (4*s))*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)) := by
  obtain ⟨G,K,hG,hK,h⟩ := exists_nativeC2Collar_series_norm_bounds (ι := AngularIndex)
  let D := 12000*Real.exp 2*(4+P.derivativeBound)
  have hD : 0 ≤ D := by have hd := P.derivativeBound_nonneg;dsimp [D];positivity
  refine ⟨D,G*D,fun k => K k*D,hD,mul_nonneg hG hD,fun k => mul_nonneg (hK k) hD,?_⟩
  intro s b hb
  have hbgt (m : Finset AngularIndex) :
      ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),(∑ i ∈ m,nativeExteriorShiftedMode P s b i x)^2)+
        (∫ x in nativePolarTimeWindow (Ioo (-1) 1),nativeCoordinateLaplacian
          (fun y => ∑ i ∈ m,nativeExteriorShiftedMode P s b i y) x^2)) ≤
        (D*Real.exp (4*s))*(∑ i ∈ m,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
    have he : 12000*Real.exp 2*Real.exp (4*s)*(4+P.derivativeBound)=D*Real.exp (4*s) := by dsimp only [D];ring
    rw [←he]
    exact nativeExteriorShiftedMode_budget P s b m
  have hh := h _ (nativeExteriorShiftedMode_C2 P s b) _ hb (fun i => sq_nonneg _) (D*Real.exp (4*s))
    (mul_nonneg hD (Real.exp_pos _).le) hbgt
  simpa only [nativeExteriorShiftedValue,nativeExteriorShiftedFirst,nativeExteriorShiftedSecond,mul_assoc] using hh

 theorem nativeExteriorShiftedValue_same_field (P : NativeHighPotential) (s : ℝ) 
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativePoissonExteriorCurve P b t : S → ℝ)) :
    (nativeExteriorShiftedValue P s b : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  let U (t : ℝ) : AngularL2 := Real.exp (2*s) • nativePoissonExteriorCurve P b (t+s)
  have hU : Continuous U := (nativePoissonExteriorCurve_continuous P b).comp
    (continuous_id.add_const s) |>.const_smul (Real.exp (2*s))
  have hf (m : Finset AngularIndex) : cylinderLift (projectedAngular m U)=fun x => ∑ i ∈ m,nativeExteriorShiftedMode P s b i x := by
    rw [nativeExteriorShiftedMode_sum P s b m]
    unfold projectedAngular
    simp only [U,real_inner_smul_right,nativePoissonExteriorCurve_coefficient]
    rw [finitePhysical_eq_lift]
    rfl
  have he := nativeCollarSeries_eq_lift _ (nativeExteriorShiftedMode_C2 P s b)
    (nativeExteriorShifted_summable P s b hb).1 U hU hf
    (weightedCylinderShift_measurable s hw) (weightedCylinderShift_representation s hae)
  filter_upwards [he] with x hx
  exact hx.trans (cylinderLift_weightedCylinderShift s w x)

#print axioms nativeExteriorShifted_summable
#print axioms nativeExteriorShifted_H2_same_jets
#print axioms exists_nativeExteriorShifted_H2_bounds
#print axioms nativeExteriorShiftedValue_same_field
end Yamabe3.Analysis.SpherePolar
