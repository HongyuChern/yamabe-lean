import Yamabe3.Analysis.DensityCutoffCommutatorIdentity
import Yamabe3.Analysis.NativeCollarJetWeakDerivatives
import Yamabe3.Analysis.NativeCollarLiftRepresentative

/-! The complete native density-divergence cutoff commutator as one
actual continuous linear collar operator. It retains both mixed terms
and the true first derivatives of the same coefficient matrix. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

private theorem comm_partial_smooth {f:E→ℝ} (hf:ContDiff ℝ ∞ f) (i:Fin 3) :
    ContDiff ℝ ∞ (partialDeriv i f) :=
  (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

def densityCutoffFirstCoefficient (A:E→Matrix (Fin 3) (Fin 3) ℝ) (χ:E→ℝ) (j:Fin 3) (x:E) : ℝ :=
  ∑i:Fin 3,(A x j i+A x i j)*partialDeriv i χ x

def densityCutoffZerothCoefficient (A:E→Matrix (Fin 3) (Fin 3) ℝ) (χ:E→ℝ) (x:E) : ℝ :=
  (∑i:Fin 3,∑j:Fin 3,A x i j*partialDeriv i (partialDeriv j χ) x)+
    ∑j:Fin 3,(∑i:Fin 3,partialDeriv i (fun y=>A y i j) x)*partialDeriv j χ x

private theorem first_smooth (A:E→Matrix (Fin 3) (Fin 3) ℝ)
    (hA:∀i j,ContDiff ℝ ∞ (fun x=>A x i j)) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (j:Fin 3) :
    ContDiff ℝ ∞ (densityCutoffFirstCoefficient A χ j) :=
  ContDiff.sum fun i _=>(hA j i |>.add (hA i j)).mul (comm_partial_smooth hχ i)

private theorem zeroth_smooth (A:E→Matrix (Fin 3) (Fin 3) ℝ)
    (hA:∀i j,ContDiff ℝ ∞ (fun x=>A x i j)) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (densityCutoffZerothCoefficient A χ) :=
  (ContDiff.sum fun i _=>ContDiff.sum fun j _=>
    (hA i j).mul (comm_partial_smooth (comm_partial_smooth hχ j) i)).add
    (ContDiff.sum fun j _=>(ContDiff.sum fun i _=>comm_partial_smooth (hA i j) i).mul
      (comm_partial_smooth hχ j))

def densityCutoffCollarCLM (A:E→Matrix (Fin 3) (Fin 3) ℝ)
    (hA:∀i j,ContDiff ℝ ∞ (fun x=>A x i j)) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    NativeCollarJet →L[ℝ] NativeCollarL2 :=
  nativeCollarJetPerturbationCLM (fun _ _ _=>0)
    (densityCutoffFirstCoefficient A χ) (densityCutoffZerothCoefficient A χ)
    (fun _ _=>continuous_const) (fun j=>(first_smooth A hA χ hχ j).continuous)
    (zeroth_smooth A hA χ hχ).continuous

theorem densityCutoffCollarCLM_C2_ae (A:E→Matrix (Fin 3) (Fin 3) ℝ)
    (hA:∀i j,ContDiff ℝ ∞ (fun x=>A x i j)) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (u:nativeC2OffZero) :
    (densityCutoffCollarCLM A hA χ hχ (nativeC2CollarJetLinear u):E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      densityCutoffCommutator A χ u.val := by
  have hrow:=nativeCollarJetPerturbationCLM_ae (fun _ _ _=>0)
    (densityCutoffFirstCoefficient A χ) (densityCutoffZerothCoefficient A χ)
    (fun _ _=>continuous_const) (fun j=>(first_smooth A hA χ hχ j).continuous)
    (zeroth_smooth A hA χ hχ).continuous (nativeC2CollarJetLinear u)
  filter_upwards [hrow,(nativeC2Collar_memLp u.property).1.coeFn_toLp,
    eventually_all.mpr (fun j=>(nativeC2Collar_memLp u.property).2.1 j |>.coeFn_toLp)] with x hr hv hp
  dsimp only [densityCutoffCollarCLM]
  rw [hr]
  change (∑i:Fin 3,∑j:Fin 3,0*(nativeC2CollarSecond u.property i j:E→ℝ) x)+
    (∑j:Fin 3,densityCutoffFirstCoefficient A χ j x*(nativeC2CollarFirst u.property j:E→ℝ) x)+
      densityCutoffZerothCoefficient A χ x*(nativeC2CollarValue u.property:E→ℝ) x=_
  simp only [zero_mul,Finset.sum_const_zero,zero_add,nativeC2CollarFirst,nativeC2CollarValue,hv,hp,densityCutoffFirstCoefficient,
    densityCutoffZerothCoefficient,densityCutoffCommutator,nativeCoordinateFirst,partialDeriv,Fin.sum_univ_three]
  ring

theorem densityCutoffCollarCLM_principal_difference (A:E→Matrix (Fin 3) (Fin 3) ℝ)
    (hA:∀i j,ContDiff ℝ ∞ (fun x=>A x i j)) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (u:nativeC2OffZero) :
    (densityCutoffCollarCLM A hA χ hχ (nativeC2CollarJetLinear u):E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun x=>χ x*principalSource A u.val x-principalSource A (fun y=>χ y*u.val y) x := by
  apply (densityCutoffCollarCLM_C2_ae A hA χ hχ u).trans
  filter_upwards [ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx
  exact densityCutoffCommutator_eq_principal_difference A hA isClosed_singleton.isOpen_compl
    ((hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn) u.property
    (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx))

#print axioms densityCutoffCollarCLM_C2_ae
#print axioms densityCutoffCollarCLM_principal_difference
end Yamabe3.Analysis.UniformElliptic
