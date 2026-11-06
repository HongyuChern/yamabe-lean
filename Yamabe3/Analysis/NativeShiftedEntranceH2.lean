import Yamabe3.Analysis.NativeShiftedEntranceFinite
import Yamabe3.Analysis.NativeC2CollarSeriesNorm
import Yamabe3.Analysis.NativePoissonReflectedCurve
import Yamabe3.Analysis.NativeWeightedLift
import Yamabe3.Analysis.NativeCollarSeriesIdentification

/-! Uniform genuine H2 jets throughout the bounded entrance range,
with one fixed reflection and one fixed original Poisson datum. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativeShiftedEntranceMode (P : NativeHighPotential) (s : ℝ) (b : AngularH1) (i : AngularIndex) : E → ℝ :=
  finitePhysical {i} (nativeShiftedEntranceCoefficient P b s)

theorem nativeShiftedEntranceMode_C2 (P : NativeHighPotential) (s : ℝ) (b : AngularH1) (i : AngularIndex) :
    ContDiffOn ℝ 2 (nativeShiftedEntranceMode P s b i) ({0}ᶜ : Set E) :=
  finitePhysical_contDiffOn_offZero_C2 {i} _ (fun j _ => nativeShiftedEntranceCoefficient_C2 P b s j)

theorem nativeShiftedEntranceMode_sum (P : NativeHighPotential) (s : ℝ) (b : AngularH1) (m : Finset AngularIndex) :
    (fun x => ∑ i ∈ m,nativeShiftedEntranceMode P s b i x)=finitePhysical m (nativeShiftedEntranceCoefficient P b s) := by
  funext x
  simp [nativeShiftedEntranceMode,finitePhysical]

 theorem nativeShiftedEntranceMode_budget (P : NativeHighPotential) (s : ℝ) (hs : s ≤ 2)
    (b : AngularH1) (m : Finset AngularIndex) :
    ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),(∑ i ∈ m,nativeShiftedEntranceMode P s b i x)^2)+
      (∫ x in nativePolarTimeWindow (Ioo (-1) 1),
        nativeCoordinateLaplacian (fun y => ∑ i ∈ m,nativeShiftedEntranceMode P s b i y) x^2)) ≤
          (12000*Real.exp 2*Real.exp 8*(4+P.derivativeBound))*
            (∑ i ∈ m,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  have h := (nativeShiftedEntranceFinite_energy P b s hs m).2.2.2
  simpa only [←nativeShiftedEntranceMode_sum P s b m] using h

def nativeShiftedEntranceValue (P : NativeHighPotential) (s : ℝ) (b : AngularH1) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarValue (nativeShiftedEntranceMode_C2 P s b i)
def nativeShiftedEntranceFirst (P : NativeHighPotential) (s : ℝ) (b : AngularH1) (j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarFirst (nativeShiftedEntranceMode_C2 P s b i) j
def nativeShiftedEntranceSecond (P : NativeHighPotential) (s : ℝ) (b : AngularH1) (k j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarSecond (nativeShiftedEntranceMode_C2 P s b i) k j

 theorem nativeShiftedEntrance_summable (P : NativeHighPotential) (s : ℝ) (hs : s ≤ 2)
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    Summable (fun i => nativeC2CollarValue (nativeShiftedEntranceMode_C2 P s b i)) ∧
      (∀ j,Summable (fun i => nativeC2CollarFirst (nativeShiftedEntranceMode_C2 P s b i) j)) ∧
      (∀ k j,Summable (fun i => nativeC2CollarSecond (nativeShiftedEntranceMode_C2 P s b i) k j)) := by
  have hd := P.derivativeBound_nonneg
  exact nativeC2Collar_series_summable _ _ hb (fun i => sq_nonneg _)
    (by positivity) (nativeShiftedEntranceMode_budget P s hs b)

 theorem nativeShiftedEntrance_H2_same_jets (P : NativeHighPotential) (s : ℝ) (hs : s ≤ 2)
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    MemWkp 2 2 (nativeShiftedEntranceValue P s b) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativeShiftedEntranceFirst P s b j) (nativeShiftedEntranceValue P s b) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativeShiftedEntranceSecond P s b k j) (nativeShiftedEntranceFirst P s b j) nativePoissonEntranceCollar) := by
  have hd := P.derivativeBound_nonneg
  exact nativeC2Collar_series_H2 _ _ hb (fun i => sq_nonneg _)
    (by positivity) (nativeShiftedEntranceMode_budget P s hs b)

 theorem exists_uniform_nativeShiftedEntrance_H2_bounds (P : NativeHighPotential) :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0 ≤ C ∧ 0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (s : ℝ),s ≤ 2 → ∀ (b : AngularH1),NativeAngularSpectralRegular (3/2) (angularEmbedding b) →
        ‖nativeShiftedEntranceValue P s b‖^2 ≤ C*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) ∧
        (∀ j,‖nativeShiftedEntranceFirst P s b j‖^2 ≤ G*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)) ∧
        (∀ k j,‖nativeShiftedEntranceSecond P s b k j‖^2 ≤ K k*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)) := by
  obtain ⟨G,K,hG,hK,h⟩ := exists_nativeC2Collar_series_norm_bounds (ι := AngularIndex)
  let D := 12000*Real.exp 2*Real.exp 8*(4+P.derivativeBound)
  have hD : 0 ≤ D := by have hd := P.derivativeBound_nonneg;dsimp [D];positivity
  refine ⟨D,G*D,fun k => K k*D,hD,mul_nonneg hG hD,fun k => mul_nonneg (hK k) hD,?_⟩
  intro s hs b hb
  exact h _ (nativeShiftedEntranceMode_C2 P s b) _ hb (fun i => sq_nonneg _) D hD
    (nativeShiftedEntranceMode_budget P s hs b)

 theorem nativeShiftedEntranceValue_same_field (P : NativeHighPotential) (s : ℝ) (hs : s ≤ 2)
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativePoissonReflectedCurve P b t : S → ℝ)) :
    (nativeShiftedEntranceValue P s b : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  let U (t : ℝ) : AngularL2 := Real.exp (2*s) • nativePoissonReflectedCurve P b (t+s)
  have hU : Continuous U := (nativePoissonReflectedCurve_continuous P b).comp
    (continuous_id.add_const s) |>.const_smul (Real.exp (2*s))
  have hf (m : Finset AngularIndex) : cylinderLift (projectedAngular m U)=fun x => ∑ i ∈ m,nativeShiftedEntranceMode P s b i x := by
    rw [nativeShiftedEntranceMode_sum P s b m]
    unfold projectedAngular
    simp only [U,real_inner_smul_right,nativePoissonReflectedCurve_coefficient]
    rw [finitePhysical_eq_lift]
    rfl
  have he := nativeCollarSeries_eq_lift _ (nativeShiftedEntranceMode_C2 P s b)
    (nativeShiftedEntrance_summable P s hs b hb).1 U hU hf
    (weightedCylinderShift_measurable s hw) (weightedCylinderShift_representation s hae)
  filter_upwards [he] with x hx
  exact hx.trans (cylinderLift_weightedCylinderShift s w x)

#print axioms nativeShiftedEntrance_summable
#print axioms nativeShiftedEntrance_H2_same_jets
#print axioms exists_uniform_nativeShiftedEntrance_H2_bounds
#print axioms nativeShiftedEntranceValue_same_field
end Yamabe3.Analysis.SpherePolar
