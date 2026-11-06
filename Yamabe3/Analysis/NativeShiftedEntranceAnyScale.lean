import Yamabe3.Analysis.NativePoissonAllScaleH2

/-! At each fixed scale the original reflected finite modes converge in
H2. This auxiliary bound may grow with the scale; the separate all-scale
uniform bound is unchanged. It permits identification of the actual PDE
on the positive-time portion without assigning a PDE to the reflection. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

 theorem nativeShiftedEntranceEnergy_any_scale (P : NativeHighPotential)
    (b : AngularH1) (s : ℝ) (i : AngularIndex) :
    let z := nativeShiftedEntranceCoefficient P b s i
    Integrable (fun t => z t^2) ∧ Integrable (fun t => deriv z t^2) ∧
      Integrable (fun t => deriv (deriv z) t^2) ∧
      nativeShiftedEntranceEnergy P b s i ≤
        (4000*Real.exp (4*s)*(4+P.derivativeBound))*nativeAngularWeightedSquare (3/2) (angularEmbedding b) i := by
  have hI := P.reflected_energy_spectral_bound b i
  have hC := P.entranceExtension_C2 b i
  dsimp only
  refine ⟨weightedTimeShift_square_integrable s hI.1,?_,?_,?_⟩
  · change Integrable (fun t => deriv (weightedTimeShift s (nativePoissonEntranceExtension P b i)) t^2)
    rw [weightedTimeShift_deriv s (hC.differentiable (by norm_num))]
    exact weightedTimeShift_square_integrable s hI.2.1
  · change Integrable (fun t => deriv (deriv (weightedTimeShift s (nativePoissonEntranceExtension P b i))) t^2)
    rw [weightedTimeShift_second s hC]
    exact weightedTimeShift_square_integrable s hI.2.2.1
  · rw [nativeShiftedEntranceEnergy_eq]
    exact (mul_le_mul_of_nonneg_left hI.2.2.2 (Real.exp_pos _).le).trans_eq (by ring)

theorem nativeShiftedEntranceFinite_any_scale (P : NativeHighPotential) (b : AngularH1)
    (τ : ℝ) (s : Finset AngularIndex) :
    let u := finitePhysical s (nativeShiftedEntranceCoefficient P b τ)
    let O := nativePolarTimeWindow (Ioo (-1) 1)
    ContDiffOn ℝ 2 u ({0}ᶜ : Set E) ∧
    IntegrableOn (fun x => u x^2) O ∧
    IntegrableOn (fun x => nativeCoordinateLaplacian u x^2) O ∧
      ((∫ x in O,u x^2)+(∫ x in O,nativeCoordinateLaplacian u x^2)) ≤
        (12000*Real.exp 2*Real.exp (4*τ)*(4+P.derivativeBound))*
          (∑ i ∈ s,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  let q := nativeShiftedEntranceCoefficient P b τ
  have hq (i : AngularIndex) : ContDiff ℝ 2 (q i) := nativeShiftedEntranceCoefficient_C2 P b τ i
  have hI (i : AngularIndex) := nativeShiftedEntranceEnergy_any_scale P b τ i
  have h0 := native_finitePhysical_collar_value_energy s q (fun i _ => hq i) (fun i _ => (hI i).1)
  have h2 := native_finitePhysical_collar_laplacian_energy s q (fun i _ => hq i)
    (fun i _ => (hI i).1) (fun i _ => (hI i).2.2.1)
  have hnon (i : AngularIndex) : 0 ≤ nativeShiftedEntranceEnergy P b τ i := by
    unfold nativeShiftedEntranceEnergy
    dsimp only
    positivity
  have hlower (i : AngularIndex) :
      (∫ t : ℝ,q i t^2) ≤ nativeShiftedEntranceEnergy P b τ i ∧
      ((∫ t : ℝ,deriv (deriv (q i)) t^2)+angularEnergyWeight i^4*(∫ t : ℝ,q i t^2)) ≤
        nativeShiftedEntranceEnergy P b τ i := by
    have hEig : 0 ≤ angularEigenvalue i := by
      rcases angularEigenvalue_zero_two_or_ge_six i with h | h | h <;> linarith
    have hw : 1 ≤ angularEnergyWeight i^4 := by
      rw [show angularEnergyWeight i^4=(angularEnergyWeight i^2)^2 by ring,angularEnergyWeight_sq]
      nlinarith only [hEig]
    have hv : 0 ≤ ∫ t : ℝ,q i t^2 := integral_nonneg (fun t => sq_nonneg (q i t))
    have hd : 0 ≤ ∫ t : ℝ,deriv (q i) t^2 := integral_nonneg (fun t => sq_nonneg (deriv (q i) t))
    have hdd : 0 ≤ ∫ t : ℝ,deriv (deriv (q i)) t^2 := integral_nonneg (fun t => sq_nonneg (deriv (deriv (q i)) t))
    have hm := mul_le_mul_of_nonneg_right hw hv
    have hn := mul_nonneg (sq_nonneg (angularEnergyWeight i)) hd
    unfold nativeShiftedEntranceEnergy
    dsimp only
    change _ ≤ _ ∧ _ ≤ _
    dsimp only [q] at hv hd hdd hm hn
    constructor <;> nlinarith only [hv,hd,hdd,hm,hn]
  have hsum0 := Finset.sum_le_sum (fun i (_ : i ∈ s) => (hlower i).1)
  have hsum2 := Finset.sum_le_sum (fun i (_ : i ∈ s) => (hlower i).2)
  have hfinite : (∑ i ∈ s,nativeShiftedEntranceEnergy P b τ i) ≤
      (4000*Real.exp (4*τ)*(4+P.derivativeBound))*(∑ i ∈ s,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hI i).2.2.2)
  have he0 := h0.2.trans (mul_le_mul_of_nonneg_left hsum0 (Real.exp_pos 2).le)
  have he2 := h2.2.trans (mul_le_mul_of_nonneg_left hsum2 (by positivity))
  have he := mul_le_mul_of_nonneg_left hfinite (by positivity : 0 ≤ 3*Real.exp 2)
  refine ⟨finitePhysical_contDiffOn_offZero_C2 s q (fun i _ => hq i),h0.1,h2.1,?_⟩
  nlinarith only [he0,he2,he]

 theorem nativeShiftedEntranceMode_any_scale_budget (P : NativeHighPotential) (s : ℝ) 
    (b : AngularH1) (m : Finset AngularIndex) :
    ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),(∑ i ∈ m,nativeShiftedEntranceMode P s b i x)^2)+
      (∫ x in nativePolarTimeWindow (Ioo (-1) 1),
        nativeCoordinateLaplacian (fun y => ∑ i ∈ m,nativeShiftedEntranceMode P s b i y) x^2)) ≤
          (12000*Real.exp 2*Real.exp (4*s)*(4+P.derivativeBound))*
            (∑ i ∈ m,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  have h := (nativeShiftedEntranceFinite_any_scale P b s m).2.2.2
  simpa only [←nativeShiftedEntranceMode_sum P s b m] using h

 theorem nativeShiftedEntrance_any_scale_summable (P : NativeHighPotential) (s : ℝ) 
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    Summable (fun i => nativeC2CollarValue (nativeShiftedEntranceMode_C2 P s b i)) ∧
      (∀ j,Summable (fun i => nativeC2CollarFirst (nativeShiftedEntranceMode_C2 P s b i) j)) ∧
      (∀ k j,Summable (fun i => nativeC2CollarSecond (nativeShiftedEntranceMode_C2 P s b i) k j)) := by
  have hd := P.derivativeBound_nonneg
  exact nativeC2Collar_series_summable _ _ hb (fun i => sq_nonneg _)
    (by positivity) (nativeShiftedEntranceMode_any_scale_budget P s b)

 theorem nativeShiftedEntrance_any_scale_H2_same_jets (P : NativeHighPotential) (s : ℝ) 
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    MemWkp 2 2 (nativeShiftedEntranceValue P s b) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativeShiftedEntranceFirst P s b j) (nativeShiftedEntranceValue P s b) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativeShiftedEntranceSecond P s b k j) (nativeShiftedEntranceFirst P s b j) nativePoissonEntranceCollar) := by
  have hd := P.derivativeBound_nonneg
  exact nativeC2Collar_series_H2 _ _ hb (fun i => sq_nonneg _)
    (by positivity) (nativeShiftedEntranceMode_any_scale_budget P s b)

 theorem nativeShiftedEntranceValue_any_scale_same_field (P : NativeHighPotential) (s : ℝ) 
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
    (nativeShiftedEntrance_any_scale_summable P s b hb).1 U hU hf
    (weightedCylinderShift_measurable s hw) (weightedCylinderShift_representation s hae)
  filter_upwards [he] with x hx
  exact hx.trans (cylinderLift_weightedCylinderShift s w x)

#print axioms nativeShiftedEntranceFinite_any_scale
#print axioms nativeShiftedEntrance_any_scale_summable
#print axioms nativeShiftedEntrance_any_scale_H2_same_jets
#print axioms nativeShiftedEntranceValue_any_scale_same_field
end Yamabe3.Analysis.SpherePolar
