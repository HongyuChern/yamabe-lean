import Yamabe3.Analysis.NativePoissonReflectedEnergy

/-! The exterior uses actual reversed cylinder time, not the artificial
negative-time extension of an interior solution. Reflection preserves
whole-line energy and reverses precisely the first derivative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def nativePoissonExteriorExtension (P : NativeHighPotential) (b : AngularH1)
    (i : AngularIndex) (t : ℝ) : ℝ := nativePoissonEntranceExtension P b i (-t)

theorem NativeHighPotential.exteriorExtension_C2 (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    ContDiff ℝ 2 (nativePoissonExteriorExtension P b i) :=
  (P.entranceExtension_C2 b i).comp contDiff_id.neg

theorem NativeHighPotential.exteriorExtension_derivatives (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    deriv (nativePoissonExteriorExtension P b i)=(fun t=> -deriv (nativePoissonEntranceExtension P b i) (-t)) ∧
    deriv (deriv (nativePoissonExteriorExtension P b i))=(fun t=>deriv (deriv (nativePoissonEntranceExtension P b i)) (-t)) := by
  let f := nativePoissonEntranceExtension P b i
  have hf := P.entranceExtension_C2 b i
  have h1 : deriv (nativePoissonExteriorExtension P b i)=(fun t=> -deriv f (-t)) := by
    funext t
    have h := ((hf.differentiable (by norm_num)) (-t)).hasDerivAt.comp t (hasDerivAt_id t).neg
    change deriv (fun x => nativePoissonEntranceExtension P b i (-x)) t = -deriv (nativePoissonEntranceExtension P b i) (-t)
    exact h.deriv.trans (by ring)
  refine ⟨h1,?_⟩
  rw [h1]
  have hd : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
  funext t
  have h := (((hd.differentiable (by norm_num)) (-t)).hasDerivAt.comp t (hasDerivAt_id t).neg).neg
  exact h.deriv.trans (by ring)

def nativePoissonExteriorSecondEnergy (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) : ℝ :=
  let z := nativePoissonExteriorExtension P b i
  let w := angularEnergyWeight i
  w^4*(∫t : ℝ,z t^2)+w^2*(∫t : ℝ,deriv z t^2)+(∫t : ℝ,deriv (deriv z) t^2)

theorem nativePoissonExteriorSecondEnergy_eq (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    nativePoissonExteriorSecondEnergy P b i=nativePoissonReflectedSecondEnergy P b i := by
  unfold nativePoissonExteriorSecondEnergy nativePoissonReflectedSecondEnergy
  dsimp only
  rw [(P.exteriorExtension_derivatives b i).2,(P.exteriorExtension_derivatives b i).1]
  simp only [nativePoissonExteriorExtension,neg_sq]
  rw [integral_neg_eq_self (fun t => nativePoissonEntranceExtension P b i t^2),
    integral_neg_eq_self (fun t => deriv (nativePoissonEntranceExtension P b i) t^2),
    integral_neg_eq_self (fun t => deriv (deriv (nativePoissonEntranceExtension P b i)) t^2)]

theorem NativeHighPotential.exterior_energy_spectral_bound (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    let z := nativePoissonExteriorExtension P b i
    Integrable (fun t=>z t^2) ∧ Integrable (fun t=>deriv z t^2) ∧
      Integrable (fun t=>deriv (deriv z) t^2) ∧
      nativePoissonExteriorSecondEnergy P b i ≤
        (4000*(4+P.derivativeBound))*nativeAngularWeightedSquare (3/2) (angularEmbedding b) i := by
  have h := P.reflected_energy_spectral_bound b i
  dsimp only
  refine ⟨h.1.comp_neg,?_,?_,?_⟩
  · rw [(P.exteriorExtension_derivatives b i).1]
    simpa only [neg_sq] using h.2.1.comp_neg
  · rw [(P.exteriorExtension_derivatives b i).2]
    exact h.2.2.1.comp_neg
  · rw [nativePoissonExteriorSecondEnergy_eq]
    exact h.2.2.2

theorem NativeHighPotential.exteriorExtension_jets (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex)
    (t : ℝ) (ht : t ≤ 0) :
    nativePoissonExteriorExtension P b i t=nativePoissonCoordinate P b i (-t) ∧
    deriv (nativePoissonExteriorExtension P b i) t= -inner ℝ (angularBasis i) (P.curveDerivative b (-t)) ∧
    deriv (deriv (nativePoissonExteriorExtension P b i)) t=
      (nativeAngularRate i^2-P.potential (-t))*nativePoissonCoordinate P b i (-t) := by
  have h := P.entranceExtension_jets b i (-t) (neg_nonneg.mpr ht)
  refine ⟨h.1,?_,?_⟩
  · rw [(P.exteriorExtension_derivatives b i).1]
    dsimp only
    rw [h.2.1]
  · rw [(P.exteriorExtension_derivatives b i).2]
    dsimp only
    rw [h.2.2]

#print axioms NativeHighPotential.exteriorExtension_derivatives
#print axioms nativePoissonExteriorSecondEnergy_eq
#print axioms NativeHighPotential.exterior_energy_spectral_bound
#print axioms NativeHighPotential.exteriorExtension_jets
end Yamabe3.Analysis.Delaunay
