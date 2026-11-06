import Yamabe3.Analysis.NativeBoundaryPoissonLinearity

/-! Actual bounded linear all-scale Poisson jets for a proved boundary
producer. The same field and uniqueness of its weak derivatives give
linearity; the full three-halves boundary energy gives boundedness. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (T : X →L[ℝ] AngularH1)
  (hT : ∀x,NativeAngularSpectralRegular (3/2) (angularEmbedding (T x)))
  (hE : ∃D : ℝ,0≤D ∧ ∀x,nativePoissonBoundaryEnergy (T x)≤D*‖x‖^2)

private theorem sqrt_bound {Y : Type*} [NormedAddCommGroup Y]
    (x : X) (y : Y) {C : ℝ} (hC : 0≤C) (h : ‖y‖^2≤C*‖x‖^2) : ‖y‖≤Real.sqrt C*‖x‖ := by
  have hs : (Real.sqrt C*‖x‖)^2=C*‖x‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  nlinarith [norm_nonneg y,mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg x)]

include hT hE in
theorem exists_nativeBoundaryPoisson_all_scale_bounds :
    ∃(C G : ℝ) (K : Fin 3 → ℝ),0≤C ∧ 0≤G ∧ (∀k,0≤K k) ∧
      ∀(x : X) (s : ℝ),
        ‖nativePoissonAllScaleValue P hp s (T x)‖≤C*‖x‖ ∧
        (∀j,‖nativePoissonAllScaleFirst P hp s (T x) j‖≤G*‖x‖) ∧
        (∀k j,‖nativePoissonAllScaleSecond P hp s (T x) k j‖≤K k*‖x‖) := by
  obtain ⟨D,hD,he⟩ := hE
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_uniform_nativePoissonAllScale_H2_bounds P hp
  refine ⟨Real.sqrt (C*D),Real.sqrt (G*D),fun k => Real.sqrt (K k*D),
    Real.sqrt_nonneg _,Real.sqrt_nonneg _,fun k => Real.sqrt_nonneg _,fun x s => ?_⟩
  have hh := h (T x) (hT x) s
  refine ⟨sqrt_bound x _ (mul_nonneg hC hD) ?_,fun j => sqrt_bound x _ (mul_nonneg hG hD) ?_,
    fun k j => sqrt_bound x _ (mul_nonneg (hK k) hD) ?_⟩
  · exact hh.1.trans ((mul_le_mul_of_nonneg_left (he x) hC).trans_eq (by ring))
  · exact (hh.2.1 j).trans ((mul_le_mul_of_nonneg_left (he x) hG).trans_eq (by ring))
  · exact (hh.2.2 k j).trans ((mul_le_mul_of_nonneg_left (he x) (hK k)).trans_eq (by ring))

def nativeBoundaryPoissonValueLinear (s : ℝ) : X →ₗ[ℝ] NativeCollarL2 where
  toFun x := nativePoissonAllScaleValue P hp s (T x)
  map_add' := nativeBoundaryPoissonValue_add P hp T hT s
  map_smul' := nativeBoundaryPoissonValue_smul P hp T hT s

def nativeBoundaryPoissonFirstLinear (s : ℝ) (j : Fin 3) : X →ₗ[ℝ] NativeCollarL2 :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) j
    (nativeBoundaryPoissonValueLinear P hp T hT s)
    (fun x => nativePoissonAllScaleFirst P hp s (T x) j)
    (fun x => (nativePoissonAllScale_H2_same_jets P hp s (T x) (hT x)).2.1 j)

def nativeBoundaryPoissonSecondLinear (s : ℝ) (k j : Fin 3) : X →ₗ[ℝ] NativeCollarL2 :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) k
    (nativeBoundaryPoissonFirstLinear P hp T hT s j)
    (fun x => nativePoissonAllScaleSecond P hp s (T x) k j)
    (fun x => (nativePoissonAllScale_H2_same_jets P hp s (T x) (hT x)).2.2 k j)

def nativeBoundaryPoissonValueCLM (s : ℝ) : X →L[ℝ] NativeCollarL2 :=
  (nativeBoundaryPoissonValueLinear P hp T hT s).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeBoundaryPoisson_all_scale_bounds P hp T hT hE
    exact ⟨C,fun x => (h x s).1⟩)
def nativeBoundaryPoissonFirstCLM (s : ℝ) (j : Fin 3) : X →L[ℝ] NativeCollarL2 :=
  (nativeBoundaryPoissonFirstLinear P hp T hT s j).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeBoundaryPoisson_all_scale_bounds P hp T hT hE
    exact ⟨G,fun x => (h x s).2.1 j⟩)
def nativeBoundaryPoissonSecondCLM (s : ℝ) (k j : Fin 3) : X →L[ℝ] NativeCollarL2 :=
  (nativeBoundaryPoissonSecondLinear P hp T hT s k j).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeBoundaryPoisson_all_scale_bounds P hp T hT hE
    exact ⟨K k,fun x => (h x s).2.2 k j⟩)

def nativeBoundaryPoissonRawJetCLM (s : ℝ) : X →L[ℝ] NativeCollarJet :=
  (nativeBoundaryPoissonValueCLM P hp T hT hE s).prod
    ((ContinuousLinearMap.pi (nativeBoundaryPoissonFirstCLM P hp T hT hE s)).prod
      (ContinuousLinearMap.pi (fun k => ContinuousLinearMap.pi (nativeBoundaryPoissonSecondCLM P hp T hT hE s k))))

theorem nativeBoundaryPoissonRawJet_mem (s : ℝ) (x : X) :
    nativeBoundaryPoissonRawJetCLM P hp T hT hE s x∈nativeCollarJetClosure :=
  nativePoissonAllScaleRawJet_mem P hp s (T x) (hT x)

def nativeBoundaryPoissonJetCLM (s : ℝ) : X →L[ℝ] nativeCollarJetClosure :=
  (nativeBoundaryPoissonRawJetCLM P hp T hT hE s).codRestrict nativeCollarJetClosure
    (nativeBoundaryPoissonRawJet_mem P hp T hT hE s)

#print axioms exists_nativeBoundaryPoisson_all_scale_bounds
#print axioms nativeBoundaryPoissonValueCLM
#print axioms nativeBoundaryPoissonFirstCLM
#print axioms nativeBoundaryPoissonSecondCLM
#print axioms nativeBoundaryPoissonRawJet_mem
end Yamabe3.Analysis.SpherePolar
