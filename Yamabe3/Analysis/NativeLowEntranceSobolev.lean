import Yamabe3.Analysis.NativeLowEntranceEquation
import Yamabe3.Analysis.FiniteSmoothSobolevFamily
import Yamabe3.Analysis.NativeJacobianAnnularSobolev

/-! Fixed finite smooth bases give real Hk bounds across the unit sphere
for the same entrance lift and its real negative Laplacian. Constants
precede the orbit and source, and do not assert H2 of the low projection. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SpherePolar SphereSpectrum UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean

def nativeStationaryPhysicalBasis (a:ℝ) (i:AngularIndex) : E→ℝ :=
  cylinderLift (separableCylinder (fun t=>Real.exp (a*t)) (angularRepresentative i))

theorem nativeStationaryPhysicalBasis_smooth (a:ℝ) (i:AngularIndex) :
    ContDiffOn ℝ ∞ (nativeStationaryPhysicalBasis a i) ({(0:E)}ᶜ) := by
  intro x hx
  exact (contDiffAt_cylinderLift (smooth_separableCylinder (by fun_prop)
    (smooth_angularRepresentative i)) hx).contDiffWithinAt

theorem nativeLowEntranceLift_basis (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0≤v t ∧ v t≤1)
    (F:ℝ →ᵇ AngularL2) (x:E) :
    nativeLowEntranceLift v hv hb F x=∑i∈nativeLowIndexFinset,
      inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F 0)*nativeStationaryPhysicalBasis (-2) i x := by
  by_cases hx:x=0
  · simp [hx,nativeLowEntranceLift,finitePhysical,nativeStationaryPhysicalBasis,cylinderLift_zero]
  let y:puncturedSpace:=⟨x,hx⟩
  change (∑i∈nativeLowIndexFinset,cylinderLift (separableCylinder
    (nativeLowEntranceCoefficient v hv hb F i) (angularRepresentative i)) (y:E))=_
  apply Finset.sum_congr rfl
  intro i hi
  change cylinderLift (separableCylinder (nativeLowEntranceCoefficient v hv hb F i) (angularRepresentative i)) (y:E)=
    inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F 0)*
      cylinderLift (separableCylinder (fun t=>Real.exp (-2*t)) (angularRepresentative i)) (y:E)
  simp only [cylinderLift_coe,puncturedCylinderLift,separableCylinder,nativeLowEntranceCoefficient]
  ring

theorem nativeLowEntranceRHS_basis (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0≤v t ∧ v t≤1)
    (F:ℝ →ᵇ AngularL2) (x:E) :
    nativeLowEntranceRHS v hv hb F x=∑i∈nativeLowIndexFinset,
      inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F 0)*
        ((angularEigenvalue i-15/4)*nativeStationaryPhysicalBasis 0 i x) := by
  change physicalForcing (fun p:ℝ × S=>Real.exp (-2*p.1)*nativeLowEntranceSourceCylinder v hv hb F p) x/8=_
  rw [physicalForcing_expNegTwo]
  by_cases hx:x=0
  · simp [hx,nativeStationaryPhysicalBasis,cylinderLift_zero]
  let y:puncturedSpace:=⟨x,hx⟩
  change (-8*cylinderLift (nativeLowEntranceSourceCylinder v hv hb F) (y:E))/8=_
  simp only [nativeLowEntranceSourceCylinder,cylinderLift_coe,puncturedCylinderLift,
    nativeFiniteStationaryCylinder_apply]
  have hb0 (i:AngularIndex):nativeStationaryPhysicalBasis 0 i x=
      radialScale ‖x‖*angularRepresentative i (sphereDirection y):=by
    change cylinderLift (separableCylinder (fun t=>Real.exp (0*t)) (angularRepresentative i)) (y:E)=_
    simp only [cylinderLift_coe,puncturedCylinderLift,separableCylinder,zero_mul,Real.exp_zero,one_mul]
    rfl
  simp_rw [hb0,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [cylinderCoordinates,y]
  ring

theorem exists_uniform_low_entrance_sobolev_bounds (k:ℕ) :
    ∃C B:ℝ≥0∞,C≠⊤ ∧ B≠⊤ ∧ ∀(v:ℝ→ℝ) (hv:Continuous v)
      (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2),
      MemWkp k 2 (nativeLowEntranceLift v hv hb F) halfEndSourceAnnulus ∧
      iteratedWeakSobolevNorm k 2 (nativeLowEntranceLift v hv hb F) halfEndSourceAnnulus≤C*ENNReal.ofReal ‖F‖ ∧
      MemWkp k 2 (nativeLowEntranceRHS v hv hb F) halfEndSourceAnnulus ∧
      iteratedWeakSobolevNorm k 2 (nativeLowEntranceRHS v hv hb F) halfEndSourceAnnulus≤B*ENNReal.ofReal ‖F‖ := by
  have hsub:closure halfEndSourceAnnulus⊆({(0:E)}ᶜ):=by
    intro x hx
    have hh:=NativeJacobianAnnulus.closure_sourceAnnulus_subset_outer hx
    change x≠0
    exact norm_pos_iff.mp (by linarith [hh.1])
  obtain ⟨C,hC,hc⟩:=exists_finite_smooth_sobolev_bound nativeLowIndexFinset
    (nativeStationaryPhysicalBasis (-2)) k halfEndSourceAnnulus_isOpen
    NativeJacobianAnnulus.sourceAnnulus_precompact isClosed_singleton.isOpen_compl hsub
    (fun i _=>nativeStationaryPhysicalBasis_smooth (-2) i)
  obtain ⟨B,hB,hb⟩:=exists_finite_smooth_sobolev_bound nativeLowIndexFinset
    (fun i x=>(angularEigenvalue i-15/4)*nativeStationaryPhysicalBasis 0 i x) k halfEndSourceAnnulus_isOpen
    NativeJacobianAnnulus.sourceAnnulus_precompact isClosed_singleton.isOpen_compl hsub
    (fun i _=>contDiffOn_const.mul (nativeStationaryPhysicalBasis_smooth 0 i))
  refine ⟨C*2,B*2,by finiteness,by finiteness,?_⟩
  intro v hv hvb F
  let c:AngularIndex→ℝ:=fun i=>inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hvb F 0)
  have hcb:∀i∈nativeLowIndexFinset,‖c i‖≤2*‖F‖:=fun i _=>(nativeLowSolvedCurve_coordinate_bounds v hv hvb F i 0).1
  have hh:=hc c (2*‖F‖) hcb
  have hg:=hb c (2*‖F‖) hcb
  have he: (fun x=>∑i∈nativeLowIndexFinset,c i*nativeStationaryPhysicalBasis (-2) i x)=
      nativeLowEntranceLift v hv hvb F:=(funext (nativeLowEntranceLift_basis v hv hvb F)).symm
  have hf: (fun x=>∑i∈nativeLowIndexFinset,c i*((angularEigenvalue i-15/4)*nativeStationaryPhysicalBasis 0 i x))=
      nativeLowEntranceRHS v hv hvb F:=(funext (nativeLowEntranceRHS_basis v hv hvb F)).symm
  rw [he] at hh
  rw [hf] at hg
  refine ⟨hh.1,?_,hg.1,?_⟩
  · simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,mul_assoc] using hh.2
  · simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,mul_assoc] using hg.2

#print axioms nativeStationaryPhysicalBasis_smooth
#print axioms nativeLowEntranceLift_basis
#print axioms nativeLowEntranceRHS_basis
#print axioms exists_uniform_low_entrance_sobolev_bounds
end Yamabe3.Analysis.Delaunay
