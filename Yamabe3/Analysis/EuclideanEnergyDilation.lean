import Yamabe3.Analysis.NativeWeakH01CompletionCore
import Yamabe3.Analysis.NativeWeakDilation
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Inclusion

/-! Exact three-dimensional energy scaling of the same compact test.
The L2 part scales by a^3 and the gradient part by a. In particular
the actual H1 norm costs sqrt(a) for 0<a≤1, not a^-1/2. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD

def euclideanDilatedDomain (a:ℝ) (O:Set E) : Set E :=
  (fun x:E => a⁻¹ • x) ⁻¹' O

def euclideanDilatedTest {a:ℝ} (ha:0<a) (O:Set E) (φ:EnergyTest D O) :
    EnergyTest D (euclideanDilatedDomain a O) :=
  ⟨fun x => φ (a⁻¹ • x),
    ((φ.smooth.contDiff).comp (contDiff_id.const_smul a⁻¹)).contMDiff,
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne')),
    fun x hx => φ.support_subset
      ((tsupport_comp_eq_preimage (φ:E→ℝ)
        (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))).le hx)⟩

theorem euclideanDilatedTest_partial {a:ℝ} (ha:0<a) (O:Set E) (φ:EnergyTest D O)
    (i:Fin 3) (x:E) :
    fderiv ℝ (euclideanDilatedTest ha O φ:E→ℝ) x (EuclideanSpace.single i 1)=
      a⁻¹*fderiv ℝ (φ:E→ℝ) (a⁻¹ • x) (EuclideanSpace.single i 1) := by
  change fderiv ℝ (fun y:E => φ (a⁻¹ • y)) x (EuclideanSpace.single i 1)=_
  rw [fderiv_comp_smul]
  rfl

theorem integral_euclidean_small_dilation {a:ℝ} (ha:0<a) (f:E→ℝ) :
    (∫x:E,f (a⁻¹ • x))=a^3*(∫x:E,f x) := by
  have hh := setIntegral_comp_dilation (r:=a⁻¹) (inv_ne_zero ha.ne') (univ:Set E) f
  simpa only [preimage_univ,Measure.restrict_univ,finrank_euclideanSpace_fin,
    inv_pow,inv_inv,abs_of_nonneg (pow_nonneg ha.le 3)] using hh

theorem euclideanDilatedTest_norm_sq {a:ℝ} (ha:0<a) (O:Set E) (φ:EnergyTest D O) :
    ‖euclideanDilatedTest ha O φ‖^2=a^3*(∫x:E,φ x^2)+
      a*(∑i:Fin 3,∫x:E,(fderiv ℝ (φ:E→ℝ) x (EuclideanSpace.single i 1))^2) := by
  rw [nativeEuclidean_test_norm_sq]
  have hvalue:(∫x:E,(euclideanDilatedTest ha O φ) x^2)=a^3*(∫x:E,φ x^2) :=
    integral_euclidean_small_dilation ha (fun x => φ x^2)
  have hgrad (i:Fin 3) :
      (∫x:E,(fderiv ℝ (euclideanDilatedTest ha O φ:E→ℝ) x (EuclideanSpace.single i 1))^2)=
        a*(∫x:E,(fderiv ℝ (φ:E→ℝ) x (EuclideanSpace.single i 1))^2) := by
    simp_rw [euclideanDilatedTest_partial,mul_pow]
    rw [integral_const_mul]
    change a⁻¹^2*(∫x:E,(fderiv ℝ (φ:E→ℝ) (a⁻¹ • x) (EuclideanSpace.single i 1))^2)=
      a*(∫x:E,(fderiv ℝ (φ:E→ℝ) x (EuclideanSpace.single i 1))^2)
    rw [integral_euclidean_small_dilation ha (fun y:E => (fderiv ℝ (φ:E→ℝ) y (EuclideanSpace.single i 1))^2)]
    field_simp
  simp_rw [hvalue,hgrad]
  rw [Finset.mul_sum]

theorem euclideanDilatedTest_norm_le {a:ℝ} (ha:0<a) (ha1:a≤1)
    (O:Set E) (φ:EnergyTest D O) :
    ‖euclideanDilatedTest ha O φ‖≤Real.sqrt a*‖φ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt ha.le,euclideanDilatedTest_norm_sq,nativeEuclidean_test_norm_sq]
  have ha3:a^3≤a := by
    have ha2:a^2≤1 := pow_le_one₀ ha.le ha1
    calc a^3=a*a^2 := by ring
         _ ≤ a*1 := mul_le_mul_of_nonneg_left ha2 ha.le
         _ = a := mul_one _
  calc
    _ ≤ a*(∫x:E,φ x^2)+a*(∑i:Fin 3,∫x:E,(fderiv ℝ (φ:E→ℝ) x (EuclideanSpace.single i 1))^2) :=
      add_le_add (mul_le_mul_of_nonneg_right ha3 (integral_nonneg fun x => sq_nonneg _)) le_rfl
    _ = _ := by ring

def euclideanDilatedTestLinear {a:ℝ} (ha:0<a) (O:Set E) :
    EnergyTest D O →ₗ[ℝ] EnergyTest D (euclideanDilatedDomain a O) where
  toFun := euclideanDilatedTest ha O
  map_add' φ ψ := by apply Subtype.ext; funext x; rfl
  map_smul' c φ := by apply Subtype.ext; funext x; rfl

#print axioms euclideanDilatedTest_partial
#print axioms integral_euclidean_small_dilation
#print axioms euclideanDilatedTest_norm_sq
#print axioms euclideanDilatedTest_norm_le
end Yamabe3.Analysis.SpherePolar
