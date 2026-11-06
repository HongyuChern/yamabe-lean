import Yamabe3.Analysis.WeakDivergenceSourceIdentity

/-! The actual normalized native weak Jacobian has the same positive
density-weighted divergence coefficients as the fixed native metric.
This identifies the divergence equation used for regularity, including
both the original annular potential and the geometric potential error. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal Manifold
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar Delaunay
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

def nativeScaledDivergenceMatrix (g : RiemannianMetric 3 E) (r : ℝ) (x : E) : Matrix (Fin 3) (Fin 3) ℝ :=
  nativeDivergenceMatrix g (r • x)

theorem nativeScaledDivergenceMatrix_posDef (g : RiemannianMetric 3 E) (r : ℝ) (x : E) :
    (nativeScaledDivergenceMatrix g r x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    exact divergenceCoefficients_symm (g:=g) (OpenPartialHomeomorph.refl E)
      contMDiff_id.contMDiffOn contMDiff_id.contMDiffOn (mem_univ _) j i
  · intro v hv
    have hv' : (WithLp.toLp 2 v : E)≠0 := fun h => hv (congrArg WithLp.ofLp h)
    have hp := divergenceCoefficients_pos (g:=g) (OpenPartialHomeomorph.refl E)
      contMDiff_id.contMDiffOn contMDiff_id.contMDiffOn (mem_univ (r • x)) (WithLp.toLp 2 v) hv'
    simpa only [nativeScaledDivergenceMatrix,nativeDivergenceMatrix,dotProduct,Matrix.mulVec,
      Pi.star_apply,star_trivial,Finset.mul_sum,PiLp.toLp_apply,mul_left_comm,mul_comm,mul_assoc] using hp

theorem nativeWeakJacobian_eq_divergence (O : Set E) (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ→ℝ) (phase : ℝ) (u : E→ℝ) :
    nativeWeakRescaledDelaunayJacobian O g r v phase u=
      fun x => weakDivergenceSource O (nativeScaledDivergenceMatrix g r) u x+
        (annularDelaunayPotential v phase x+nativeDelaunayPotentialError g r v phase x)*u x := by
  let A : E→Matrix (Fin 3) (Fin 3) ℝ := nativeScaledDivergenceMatrix g r
  have hA (i j : Fin 3) : ContDiff ℝ ∞ (fun x => A x i j) :=
    (contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r)
  have hd (i j : Fin 3) : partialDeriv i (nativeScaledPrincipalError g r i j)=partialDeriv i (fun x => A x i j) := by
    funext x
    change (fderiv ℝ (fun y : E => A y i j-(1 : Matrix (Fin 3) (Fin 3) ℝ) i j) x) (EuclideanSpace.single i 1)=
      (fderiv ℝ (fun y : E => A y i j) x) (EuclideanSpace.single i 1)
    rw [fderiv_fun_sub ((hA i j).differentiable (by simp) x) (differentiableAt_const _)]
    simp
  funext x
  let p := fun j => chosenWeakPartial' 2 j u O x
  let q := fun i j => chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O x
  have hs : (∑i : Fin 3,∑j : Fin 3,(A x i j-(1 : Matrix (Fin 3) (Fin 3) ℝ) i j)*q i j)=
      (∑i : Fin 3,∑j : Fin 3,A x i j*q i j)-(∑i : Fin 3,q i i) := by
    simp only [sub_mul,Finset.sum_sub_distrib,Matrix.one_apply,ite_mul,one_mul,zero_mul]
    simp
  have hf : (∑j : Fin 3,(∑i : Fin 3,partialDeriv i (fun y => A y i j) x)*p j)=
      ∑i : Fin 3,∑j : Fin 3,partialDeriv i (fun y => A y i j) x*p j := by
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  simp only [nativeWeakRescaledDelaunayJacobian,weakNegativeLaplacian,iterWeakPartial,
    weakSecondOrderPerturbation,nativeScaledFirstError,hd,zero_mul,add_zero,weakDivergenceSource,
    Finset.sum_add_distrib]
  change -(∑i : Fin 3,q i i)+_-((∑i : Fin 3,∑j : Fin 3,(A x i j-(1 : Matrix (Fin 3) (Fin 3) ℝ) i j)*q i j)+
    (∑j : Fin 3,(∑i : Fin 3,partialDeriv i (fun y => A y i j) x)*p j))+_=_
  rw [hs,hf]
  ring

theorem nativeWeakJacobian_divergence_equation {O : Set E} (hO : IsOpen O)
    (g : RiemannianMetric 3 E) (r : ℝ) (v : ℝ→ℝ) (phase : ℝ) {u f : E→ℝ}
    (hu : MemWkp 2 2 u O)
    (he : nativeWeakRescaledDelaunayJacobian O g r v phase u=ᵐ[volume.restrict O] f) :
    WeakEquation O (matrixFlux (nativeScaledDivergenceMatrix g r) (fun j => chosenWeakPartial' 2 j u O))
      (fun x => f x-(annularDelaunayPotential v phase x+nativeDelaunayPotentialError g r v phase x)*u x) := by
  have hw := weakEquation_weakDivergenceSource hO (nativeScaledDivergenceMatrix g r)
    (fun i j => (contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r)) hu
  rw [nativeWeakJacobian_eq_divergence] at he
  intro φ hφ hc hs
  rw [hw φ hφ hc hs]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  exact congrArg (fun z : ℝ => z*φ x) (eq_sub_of_add_eq hx)

#print axioms nativeScaledDivergenceMatrix_posDef
#print axioms nativeWeakJacobian_eq_divergence
#print axioms nativeWeakJacobian_divergence_equation
end Yamabe3.Analysis.UniformElliptic
