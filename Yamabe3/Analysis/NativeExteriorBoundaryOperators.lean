import Yamabe3.Analysis.NativeExteriorBoundaryLinearity
import Yamabe3.Analysis.NativePoissonExteriorNormBound
import Yamabe3.Analysis.NativePoissonExteriorCollarTrace

/-! Bounded linear exterior Poisson jets on the actual H2 collar,
for a proved three-halves boundary producer. -/
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
  (T : X →L[ℝ] AngularH1)
  (hT : ∀x,NativeAngularSpectralRegular (3/2) (angularEmbedding (T x)))
  (hE : ∃D : ℝ,0≤D ∧ ∀x,(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (T x)) i)≤D*‖x‖^2)

private theorem sqrt_bound {Y : Type*} [NormedAddCommGroup Y]
    (x : X) (y : Y) {C : ℝ} (hC : 0≤C) (h : ‖y‖^2≤C*‖x‖^2) : ‖y‖≤Real.sqrt C*‖x‖ := by
  have hs : (Real.sqrt C*‖x‖)^2=C*‖x‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  nlinarith [norm_nonneg y,mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg x)]

include hT hE in
theorem exists_nativeExteriorBoundary_bounds :
    ∃(C G : ℝ) (K : Fin 3 → ℝ),0≤C ∧ 0≤G ∧ (∀k,0≤K k) ∧
      ∀(x : X),
        ‖nativePoissonExteriorCollarValue P (T x)‖≤C*‖x‖ ∧
        (∀j,‖nativePoissonExteriorCollarFirst P (T x) j‖≤G*‖x‖) ∧
        (∀k j,‖nativePoissonExteriorCollarSecond P (T x) k j‖≤K k*‖x‖) := by
  obtain ⟨D,hD,he⟩ := hE
  obtain ⟨G,K,hG,hK,h⟩ := exists_nativePoissonExteriorCollar_H2_norm_bounds P
  let C : ℝ := 12000*Real.exp 2*(4+P.derivativeBound)
  have hC : 0≤C := by have h := P.derivativeBound_nonneg; dsimp [C]; positivity
  refine ⟨Real.sqrt (C*D),Real.sqrt (G*D),fun k => Real.sqrt (K k*D),
    Real.sqrt_nonneg _,Real.sqrt_nonneg _,fun k => Real.sqrt_nonneg _,fun x => ?_⟩
  have hh := h (T x) (hT x)
  refine ⟨sqrt_bound x _ (mul_nonneg hC hD) ?_,fun j => sqrt_bound x _ (mul_nonneg hG hD) ?_,
    fun k j => sqrt_bound x _ (mul_nonneg (hK k) hD) ?_⟩
  · exact hh.1.trans ((mul_le_mul_of_nonneg_left (he x) hC).trans_eq (by ring))
  · exact (hh.2.1 j).trans ((mul_le_mul_of_nonneg_left (he x) hG).trans_eq (by ring))
  · exact (hh.2.2 k j).trans ((mul_le_mul_of_nonneg_left (he x) (hK k)).trans_eq (by ring))

def nativeExteriorBoundaryValueLinear : X →ₗ[ℝ] NativeCollarL2 where
  toFun x := nativePoissonExteriorCollarValue P (T x)
  map_add' := nativeExteriorBoundaryValue_add P T hT
  map_smul' := nativeExteriorBoundaryValue_smul P T hT

def nativeExteriorBoundaryFirstLinear (j : Fin 3) : X →ₗ[ℝ] NativeCollarL2 :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) j
    (nativeExteriorBoundaryValueLinear P T hT)
    (fun x => nativePoissonExteriorCollarFirst P (T x) j)
    (fun x => (nativePoissonExteriorCollar_H2_and_strong_jets P (T x) (hT x)).2.1 j)

def nativeExteriorBoundarySecondLinear (k j : Fin 3) : X →ₗ[ℝ] NativeCollarL2 :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) k
    (nativeExteriorBoundaryFirstLinear P T hT j)
    (fun x => nativePoissonExteriorCollarSecond P (T x) k j)
    (fun x => (nativePoissonExteriorCollar_H2_and_strong_jets P (T x) (hT x)).2.2.1 k j)

def nativeExteriorBoundaryValueCLM : X →L[ℝ] NativeCollarL2 :=
  (nativeExteriorBoundaryValueLinear P T hT).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeExteriorBoundary_bounds P T hT hE
    exact ⟨C,fun x => (h x).1⟩)
def nativeExteriorBoundaryFirstCLM (j : Fin 3) : X →L[ℝ] NativeCollarL2 :=
  (nativeExteriorBoundaryFirstLinear P T hT j).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeExteriorBoundary_bounds P T hT hE
    exact ⟨G,fun x => (h x).2.1 j⟩)
def nativeExteriorBoundarySecondCLM (k j : Fin 3) : X →L[ℝ] NativeCollarL2 :=
  (nativeExteriorBoundarySecondLinear P T hT k j).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeExteriorBoundary_bounds P T hT hE
    exact ⟨K k,fun x => (h x).2.2 k j⟩)

def nativeExteriorBoundaryRawJetCLM : X →L[ℝ] NativeCollarJet :=
  (nativeExteriorBoundaryValueCLM P T hT hE).prod
    ((ContinuousLinearMap.pi (nativeExteriorBoundaryFirstCLM P T hT hE)).prod
      (ContinuousLinearMap.pi (fun k => ContinuousLinearMap.pi (nativeExteriorBoundarySecondCLM P T hT hE k))))

theorem nativeExteriorBoundaryRawJet_mem (x : X) :
    nativeExteriorBoundaryRawJetCLM P T hT hE x∈nativeCollarJetClosure :=
  nativePoissonExteriorRawJet_mem P (T x) (hT x)

def nativeExteriorBoundaryJetCLM : X →L[ℝ] nativeCollarJetClosure :=
  (nativeExteriorBoundaryRawJetCLM P T hT hE).codRestrict nativeCollarJetClosure
    (nativeExteriorBoundaryRawJet_mem P T hT hE)

#print axioms exists_nativeExteriorBoundary_bounds
#print axioms nativeExteriorBoundaryValueCLM
#print axioms nativeExteriorBoundaryFirstCLM
#print axioms nativeExteriorBoundarySecondCLM
#print axioms nativeExteriorBoundaryRawJet_mem
end Yamabe3.Analysis.SpherePolar
