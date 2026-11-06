import Yamabe3.Analysis.NativeCollarJetSpace
import Yamabe3.Analysis.NativeCollarTraceUnique

/-! Actual value and radial derivative restrictions extend continuously
from C2 functions to their strong volume H2 jet closure. Both traces are
constructed from literal sphere restrictions and proven collar bounds. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

private theorem sphere_ne_zero (θ : S) : (θ:E) ≠ 0 := by
  intro h
  have hn := norm_eq_of_mem_sphere θ
  rw [h,norm_zero] at hn
  norm_num at hn

def nativeC2ValueTraceLinear : nativeC2OffZero →ₗ[ℝ] Lp ℝ 2 angularVolume where
  toFun u := (native_C1_sphere_restriction_memLp u.property.continuousOn).toLp (fun θ : S => u.val (θ:E))
  map_add' u v := MemLp.toLp_add _ _
  map_smul' c u := MemLp.toLp_const_smul c _

def nativeC2NormalTraceLinear : nativeC2OffZero →ₗ[ℝ] Lp ℝ 2 angularVolume where
  toFun u := (native_C1_sphere_normal_memLp (u.property.of_le (by norm_num))).toLp
    (fun θ : S => fderiv ℝ u.val (θ:E) (θ:E))
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(native_C1_sphere_normal_memLp ((u+v).property.of_le (by norm_num))).coeFn_toLp,
      (native_C1_sphere_normal_memLp (u.property.of_le (by norm_num))).coeFn_toLp,
      (native_C1_sphere_normal_memLp (v.property.of_le (by norm_num))).coeFn_toLp,
      Lp.coeFn_add
        ((native_C1_sphere_normal_memLp (u.property.of_le (by norm_num))).toLp _)
        ((native_C1_sphere_normal_memLp (v.property.of_le (by norm_num))).toLp _)] with θ hsum hu hv ha
    rw [hsum,ha]
    simp only [Pi.add_apply,hu,hv]
    have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
    change fderiv ℝ (fun x => u.val x+v.val x) (θ:E) (θ:E)=_
    rw [fderiv_fun_add ((u.property.contDiffAt (hO.mem_nhds (sphere_ne_zero θ))).differentiableAt (by norm_num))
      ((v.property.contDiffAt (hO.mem_nhds (sphere_ne_zero θ))).differentiableAt (by norm_num))]
    rfl
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(native_C1_sphere_normal_memLp ((c • u).property.of_le (by norm_num))).coeFn_toLp,
      (native_C1_sphere_normal_memLp (u.property.of_le (by norm_num))).coeFn_toLp,
      Lp.coeFn_smul c ((native_C1_sphere_normal_memLp (u.property.of_le (by norm_num))).toLp _)] with θ hcu hu ha
    simp only [RingHom.id_apply]
    rw [hcu,ha]
    simp only [Pi.smul_apply,smul_eq_mul,hu]
    have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
    change fderiv ℝ (fun x => c*u.val x) (θ:E) (θ:E)=_
    rw [fderiv_const_mul ((u.property.contDiffAt (hO.mem_nhds (sphere_ne_zero θ))).differentiableAt (by norm_num))]
    rfl

theorem nativeC2CollarJet_component_bounds (u : nativeC2OffZero) :
    ‖nativeC2CollarValue u.property‖≤‖nativeC2CollarJetLinear u‖ ∧
    (∀ j,‖nativeC2CollarFirst u.property j‖≤‖nativeC2CollarJetLinear u‖) ∧
    (∀ k j,‖nativeC2CollarSecond u.property k j‖≤‖nativeC2CollarJetLinear u‖) := by
  let J := nativeC2CollarJetLinear u
  exact ⟨norm_fst_le J,fun j => (norm_le_pi_norm J.2.1 j).trans ((norm_fst_le J.2).trans (norm_snd_le J)),
    fun k j => (norm_le_pi_norm (J.2.2 k) j).trans ((norm_le_pi_norm J.2.2 k).trans
      ((norm_snd_le J.2).trans (norm_snd_le J)))⟩

theorem nativeC2Trace_norm_bounds :
    ∃ C D : ℝ,0≤C ∧ 0≤D ∧ ∀ u : nativeC2OffZero,
      ‖nativeC2ValueTraceLinear u‖≤C*‖nativeC2CollarJetLinear u‖ ∧
      ‖nativeC2NormalTraceLinear u‖≤D*‖nativeC2CollarJetLinear u‖ := by
  obtain ⟨C,hC,hvalue⟩ := exists_native_C1_collar_value_trace_bound
  obtain ⟨D,hD,hnormal⟩ := exists_native_C2_collar_normal_trace_bound
  refine ⟨Real.sqrt (4*C),Real.sqrt (12*D),Real.sqrt_nonneg _,Real.sqrt_nonneg _,fun u => ?_⟩
  let J := nativeC2CollarJetLinear u
  have hb := nativeC2CollarJet_component_bounds u
  have hv : ‖nativeC2CollarValue u.property‖^2≤‖J‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb.1
  have hp (j : Fin 3) : ‖nativeC2CollarFirst u.property j‖^2≤‖J‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hb.2.1 j)
  have hs (k j : Fin 3) : ‖nativeC2CollarSecond u.property k j‖^2≤‖J‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hb.2.2 k j)
  have hsum : (∑ j : Fin 3,‖nativeC2CollarFirst u.property j‖^2)≤3*‖J‖^2 := by
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hp j)
  have hs2 (j : Fin 3) : (∑ k : Fin 3,‖nativeC2CollarSecond u.property k j‖^2)≤3*‖J‖^2 := by
    simpa using Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hs k j)
  have hsall : (∑ j : Fin 3,(‖nativeC2CollarFirst u.property j‖^2+
      ∑ k : Fin 3,‖nativeC2CollarSecond u.property k j‖^2))≤12*‖J‖^2 := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => add_le_add (hp j) (hs2 j))
    apply hh.trans_eq
    norm_num
    ring
  have hm := nativeC2Collar_memLp u.property
  have h0 := hvalue u.val (u.property.of_le (by norm_num))
  have h1 := hnormal u.val u.property
  rw [integral_add hm.1.integrable_sq (integrable_finsetSum _ (fun j _ => (hm.2.1 j).integrable_sq)),
    integral_finsetSum _ (fun j _ => (hm.2.1 j).integrable_sq)] at h0
  have he (j : Fin 3) : (∫ x in nativePoissonEntranceCollar,
      nativeCoordinateFirst j u.val x^2+∑ k : Fin 3,nativeCoordinateSecond k j u.val x^2)=
      ‖nativeC2CollarFirst u.property j‖^2+∑ k : Fin 3,‖nativeC2CollarSecond u.property k j‖^2 := by
    rw [integral_add (hm.2.1 j).integrable_sq (integrable_finsetSum _ (fun k _ => (hm.2.2 k j).integrable_sq)),
      integral_finsetSum _ (fun k _ => (hm.2.2 k j).integrable_sq)]
    simp only [nativeC2CollarFirst,nativeC2CollarSecond,native_norm_toLp_sq_eq_integral_sq]
  simp_rw [he] at h1
  have h0' : ‖nativeC2ValueTraceLinear u‖^2≤C*(‖nativeC2CollarValue u.property‖^2+
      ∑ j : Fin 3,‖nativeC2CollarFirst u.property j‖^2) := by
    simpa only [nativeC2ValueTraceLinear,LinearMap.coe_mk,AddHom.coe_mk,nativeC2CollarValue,
      nativeC2CollarFirst,native_norm_toLp_sq_eq_integral_sq] using h0
  have h1' : ‖nativeC2NormalTraceLinear u‖^2≤D*(∑ j : Fin 3,(‖nativeC2CollarFirst u.property j‖^2+
      ∑ k : Fin 3,‖nativeC2CollarSecond u.property k j‖^2)) := by
    simpa only [nativeC2NormalTraceLinear,LinearMap.coe_mk,AddHom.coe_mk,native_norm_toLp_sq_eq_integral_sq] using h1
  have hvb := h0'.trans (mul_le_mul_of_nonneg_left (add_le_add hv hsum) hC)
  have hnb := h1'.trans (mul_le_mul_of_nonneg_left hsall hD)
  have hsq0 : (Real.sqrt (4*C)*‖J‖)^2=4*C*‖J‖^2 := by rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hsq1 : (Real.sqrt (12*D)*‖J‖)^2=12*D*‖J‖^2 := by rw [mul_pow,Real.sq_sqrt (by positivity)]
  constructor
  · nlinarith [norm_nonneg (nativeC2ValueTraceLinear u),mul_nonneg (Real.sqrt_nonneg (4*C)) (norm_nonneg J)]
  · nlinarith [norm_nonneg (nativeC2NormalTraceLinear u),mul_nonneg (Real.sqrt_nonneg (12*D)) (norm_nonneg J)]

def nativeCollarValueTraceCLM : nativeCollarJetClosure →L[ℝ] Lp ℝ 2 angularVolume :=
  nativeC2ValueTraceLinear.extendOfNorm nativeC2CollarJetInclusion

def nativeCollarNormalTraceCLM : nativeCollarJetClosure →L[ℝ] Lp ℝ 2 angularVolume :=
  nativeC2NormalTraceLinear.extendOfNorm nativeC2CollarJetInclusion

theorem nativeCollarTraceCLM_agrees_C2 (u : nativeC2OffZero) :
    nativeCollarValueTraceCLM (nativeC2CollarJetInclusion u)=nativeC2ValueTraceLinear u ∧
    nativeCollarNormalTraceCLM (nativeC2CollarJetInclusion u)=nativeC2NormalTraceLinear u := by
  obtain ⟨C,D,hC,hD,hb⟩ := nativeC2Trace_norm_bounds
  exact ⟨LinearMap.extendOfNorm_eq nativeC2CollarJetInclusion_dense ⟨C,fun u => (hb u).1⟩ u,
    LinearMap.extendOfNorm_eq nativeC2CollarJetInclusion_dense ⟨D,fun u => (hb u).2⟩ u⟩

#print axioms nativeC2Trace_norm_bounds
#print axioms nativeCollarTraceCLM_agrees_C2
end Yamabe3.Analysis.SpherePolar
