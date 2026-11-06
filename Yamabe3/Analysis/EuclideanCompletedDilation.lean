import Yamabe3.Analysis.EuclideanEnergyDilation
import Yamabe3.Analysis.NativeWeakChartTransport
import Yamabe3.Analysis.WeakLaplacianDilation

/-! The exact small physical dilation extends to the ORIGINAL energy
completion, with sqrt(a) norm bound and its actual dilated L2 class.
No new representative is chosen independently at different scales. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT UniformSpace
open scoped ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD
local notation "μ" => (RiemannianMetric.euclideanMetric 3).volumeMeasure

theorem ae_nativeEuclidean_dilation {a:ℝ} (ha:0<a) {f h:E→ℝ} (he:f=ᵐ[μ] h) :
    (fun x:E => f (a⁻¹ • x))=ᵐ[μ] (fun x:E => h (a⁻¹ • x)) := by
  have h0:f=ᵐ[volume.restrict (univ:Set E)] h := by
    simpa only [Measure.restrict_univ,native_euclideanMetric_volumeMeasure] using he
  simpa only [preimage_univ,Measure.restrict_univ,native_euclideanMetric_volumeMeasure] using
    ae_comp_dilation (inv_ne_zero ha.ne') h0

theorem memLp_nativeEuclidean_dilation {a:ℝ} (ha:0<a) (f:Lp ℝ 2 μ) :
    MemLp (fun x:E => f (a⁻¹ • x)) 2 μ := by
  have hf:MemLp (f:E→ℝ) 2 (volume.restrict (univ:Set E)) := by
    simpa only [Measure.restrict_univ,native_euclideanMetric_volumeMeasure] using Lp.memLp f
  simpa only [preimage_univ,Measure.restrict_univ,native_euclideanMetric_volumeMeasure] using
    memLp_comp_dilation (inv_ne_zero ha.ne') hf

def euclideanL2DilationLinear {a:ℝ} (ha:0<a) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (memLp_nativeEuclidean_dilation ha f).toLp (fun x:E => f (a⁻¹ • x))
  map_add' f h := by
    apply Lp.ext
    filter_upwards [(memLp_nativeEuclidean_dilation ha (f+h)).coeFn_toLp,
      (memLp_nativeEuclidean_dilation ha f).coeFn_toLp,
      (memLp_nativeEuclidean_dilation ha h).coeFn_toLp,
      Lp.coeFn_add ((memLp_nativeEuclidean_dilation ha f).toLp _) ((memLp_nativeEuclidean_dilation ha h).toLp _),
      ae_nativeEuclidean_dilation ha (Lp.coeFn_add f h)] with x hs hf hh ha'
        hsum
    rw [hs,ha']
    change (f+h) (a⁻¹ • x)=
      ((memLp_nativeEuclidean_dilation ha f).toLp _) x+((memLp_nativeEuclidean_dilation ha h).toLp _) x
    rw [hf,hh]
    exact hsum
  map_smul' c f := by
    apply Lp.ext
    simp only [RingHom.id_apply]
    filter_upwards [(memLp_nativeEuclidean_dilation ha (c • f)).coeFn_toLp,
      (memLp_nativeEuclidean_dilation ha f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_nativeEuclidean_dilation ha f).toLp _),
      ae_nativeEuclidean_dilation ha (Lp.coeFn_smul c f)] with x hs hf ha' hsm
    rw [hs,ha']
    change (c • f) (a⁻¹ • x)=c*((memLp_nativeEuclidean_dilation ha f).toLp _) x
    rw [hf]
    exact hsm

theorem nativeEuclideanLp_norm_sq (f:Lp ℝ 2 μ) : ‖f‖^2=∫x:E,f x^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  calc
    _ = ∫x:E,(f:E→ℝ) x^2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp only [Real.inner_apply,pow_two]
    _ = _ := congrArg (fun ν:Measure E => ∫x:E,(f:E→ℝ) x^2 ∂ν)
      (native_euclideanMetric_volumeMeasure 3)

theorem euclideanL2Dilation_norm_sq {a:ℝ} (ha:0<a) (f:Lp ℝ 2 μ) :
    ‖euclideanL2DilationLinear ha f‖^2=a^3*‖f‖^2 := by
  rw [nativeEuclideanLp_norm_sq,nativeEuclideanLp_norm_sq]
  have hae:(euclideanL2DilationLinear ha f:E→ℝ)=ᵐ[volume] (fun x:E => f (a⁻¹ • x)) := by
    simpa only [native_euclideanMetric_volumeMeasure,euclideanL2DilationLinear,LinearMap.coe_mk,AddHom.coe_mk] using (memLp_nativeEuclidean_dilation ha f).coeFn_toLp
  exact (integral_congr_ae (hae.mono fun x hx => by rw [hx])).trans
    (integral_euclidean_small_dilation ha (fun y => f y^2))

theorem euclideanL2Dilation_norm_le {a:ℝ} (ha:0<a) (ha1:a≤1) (f:Lp ℝ 2 μ) :
    ‖euclideanL2DilationLinear ha f‖≤Real.sqrt a*‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [euclideanL2Dilation_norm_sq,mul_pow,Real.sq_sqrt ha.le]
  have ha2:a^2≤1 := pow_le_one₀ ha.le ha1
  have ha3:a^3≤a := by nlinarith [mul_le_mul_of_nonneg_left ha2 ha.le]
  exact mul_le_mul_of_nonneg_right ha3 (sq_nonneg _)

def euclideanL2DilationCLM {a:ℝ} (ha:0<a) (ha1:a≤1) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (euclideanL2DilationLinear ha).mkContinuous (Real.sqrt a) (euclideanL2Dilation_norm_le ha ha1)

theorem euclideanL2DilationCLM_ae {a:ℝ} (ha:0<a) (ha1:a≤1) (f:Lp ℝ 2 μ) :
    (euclideanL2DilationCLM ha ha1 f:E→ℝ)=ᵐ[μ] (fun x:E => f (a⁻¹ • x)) :=
  (memLp_nativeEuclidean_dilation ha f).coeFn_toLp

def euclideanEnergyDilationTestToH1 {a:ℝ} (ha:0<a) (ha1:a≤1) (O:Set E) :
    EnergyTest D O →L[ℝ] H1Zero D (euclideanDilatedDomain a O) :=
  (((Completion.toComplL:EnergyTest D (euclideanDilatedDomain a O) →L[ℝ]
    H1Zero D (euclideanDilatedDomain a O)).toLinearMap).comp
      (euclideanDilatedTestLinear ha O)).mkContinuous (Real.sqrt a) (fun φ => by
        change ‖(euclideanDilatedTest ha O φ:H1Zero D (euclideanDilatedDomain a O))‖≤Real.sqrt a*‖φ‖
        rw [Completion.norm_coe]
        exact euclideanDilatedTest_norm_le ha ha1 O φ)

def euclideanH1DilationCLM {a:ℝ} (ha:0<a) (ha1:a≤1) (O:Set E) :
    H1Zero D O →L[ℝ] H1Zero D (euclideanDilatedDomain a O) :=
  (euclideanEnergyDilationTestToH1 ha ha1 O).extend Completion.toComplL

theorem euclideanH1DilationCLM_coe {a:ℝ} (ha:0<a) (ha1:a≤1) (O:Set E) (φ:EnergyTest D O) :
    euclideanH1DilationCLM ha ha1 O (φ:H1Zero D O)=
      (euclideanDilatedTest ha O φ:H1Zero D (euclideanDilatedDomain a O)) :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe (EnergyTest D O)) φ

theorem euclideanH1DilationCLM_norm_le {a:ℝ} (ha:0<a) (ha1:a≤1) (O:Set E) (z:H1Zero D O) :
    ‖euclideanH1DilationCLM ha ha1 O z‖≤Real.sqrt a*‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih φ =>
    rw [euclideanH1DilationCLM_coe,Completion.norm_coe,Completion.norm_coe]
    exact euclideanDilatedTest_norm_le ha ha1 O φ

theorem euclideanH1DilationCLM_toL2 {a:ℝ} (ha:0<a) (ha1:a≤1) (O:Set E) (z:H1Zero D O) :
    toL2 D (euclideanDilatedDomain a O) (euclideanH1DilationCLM ha ha1 O z)=
      euclideanL2DilationCLM ha ha1 (toL2 D O z) := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih φ =>
    rw [euclideanH1DilationCLM_coe,toL2_coe]
    have hin:(toL2 D O (φ:H1Zero D O):E→ℝ)=ᵐ[μ] (φ:E→ℝ) := by
      rw [toL2_coe]
      exact φ.memLp.coeFn_toLp
    apply Lp.ext
    filter_upwards [(euclideanDilatedTest ha O φ).memLp.coeFn_toLp,
      euclideanL2DilationCLM_ae ha ha1 (toL2 D O (φ:H1Zero D O)),
      ae_nativeEuclidean_dilation ha hin] with x hleft hright hinput
    exact hleft.trans (hinput.symm.trans hright.symm)

theorem euclideanH1DilationCLM_ae {a:ℝ} (ha:0<a) (ha1:a≤1) (O:Set E) (z:H1Zero D O) :
    (toL2 D (euclideanDilatedDomain a O) (euclideanH1DilationCLM ha ha1 O z):E→ℝ)=ᵐ[μ]
      (fun x:E => toL2 D O z (a⁻¹ • x)) := by
  rw [euclideanH1DilationCLM_toL2]
  exact euclideanL2DilationCLM_ae ha ha1 _

#print axioms euclideanL2Dilation_norm_sq
#print axioms euclideanH1DilationCLM_norm_le
#print axioms euclideanH1DilationCLM_toL2
#print axioms euclideanH1DilationCLM_ae
end Yamabe3.Analysis.SpherePolar
