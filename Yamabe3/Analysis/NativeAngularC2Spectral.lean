import Yamabe3.Analysis.NativeAngularC1Spectral
import Yamabe3.Analysis.NativeManifoldC2Green

/-! Original C2 angular values have the required three-halves trace
regularity. The same native Laplacian, C1/C2 Green identity and actual
Hilbert basis prove the spectral bound. No infinite smoothness is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace lp
namespace Yamabe3.Analysis.SphereSpectrum
open Poincare.Geometry.Riemannian.SpaceForm Yamabe3.Analysis.Delaunay NativeC2Green
private abbrev D := (roundSphereMetric 2).leviCivitaData
private abbrev μ := (roundSphereMetric 2).volumeMeasure

def negativeLaplacianAngularC2 (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 2 f) : AngularL2 :=
  continuousAngularL2 (fun x=> -D.laplacian f x) (continuous_laplacian_C2 D hf).neg

theorem negativeLaplacianAngularC2_coefficient (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 2 f) (i : AngularIndex) :
    inner ℝ (angularBasis i) (negativeLaplacianAngularC2 f hf)=
      angularEigenvalue i*inner ℝ (angularBasis i) (continuousAngularL2 f hf.continuous) := by
  obtain ⟨U,hU,hUae,_,hUP⟩ := exists_smooth_angular_eigenfunction i
  have h1 := integral_mul_laplacian_of_compact_C1_C2 D (hU.of_le (by simp)) hf (HasCompactSupport.of_compactSpace _)
  have h2 := integral_mul_laplacian_of_compact_C1_C2 D (hf.of_le (by norm_num)) (hU.of_le (by norm_cast)) (HasCompactSupport.of_compactSpace _)
  have hsym : (∫x,(roundSphereMetric 2).inner x (D.gradient U x) (D.gradient f x) ∂μ)=
      ∫x,(roundSphereMetric 2).inner x (D.gradient f x) (D.gradient U x) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x=>(roundSphereMetric 2).symm x _ _)
  have hcomm : (∫x,U x*(-D.laplacian f x) ∂μ)=∫x,(-D.laplacian U x)*f x ∂μ := by
    simp_rw [mul_neg,neg_mul,integral_neg]
    have hswap : (∫x,D.laplacian U x*f x ∂μ)=(∫x,f x*D.laplacian U x ∂μ) :=
      integral_congr_ae (Eventually.of_forall fun x=>mul_comm _ _)
    rw [hswap,h1,h2,hsym]
  simp only [L2.inner_def,setIntegral_univ]
  calc
    _ = ∫x,U x*(-D.laplacian f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hUae,continuousAngularL2_ae _ (continuous_laplacian_C2 D hf).neg] with x hx hfx
      change inner ℝ ((angularBasis i) x) ((negativeLaplacianAngularC2 f hf) x)=_
      change (negativeLaplacianAngularC2 f hf) x= -D.laplacian f x at hfx
      rw [←hx,hfx]
      simp [mul_comm]
    _ = ∫x,(-D.laplacian U x)*f x ∂μ := hcomm
    _ = angularEigenvalue i*(∫x,U x*f x ∂μ) := by
      simp_rw [hUP,mul_assoc]
      exact integral_const_mul _ _
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hUae,continuousAngularL2_ae f hf.continuous] with x hx hfx
      rw [←hx,hfx]
      simp [mul_comm]

theorem angular_C2_spectral_energy (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 2 f) :
    NativeAngularSpectralRegular 2 (continuousAngularL2 f hf.continuous) ∧
      (∑'i,nativeAngularWeightedSquare 2 (continuousAngularL2 f hf.continuous) i) ≤
        2*(‖continuousAngularL2 f hf.continuous‖^2+‖negativeLaplacianAngularC2 f hf‖^2) := by
  let F := continuousAngularL2 f hf.continuous
  let L := negativeLaplacianAngularC2 f hf
  let c := fun i=>inner ℝ (angularBasis i) F
  have hparse (a : AngularL2) : HasSum (fun i=>(inner ℝ (angularBasis i) a)^2) (‖a‖^2) := by
    have h := angularBasis.hasSum_inner_mul_inner a a
    simpa only [real_inner_comm a,←pow_two,real_inner_self_eq_norm_sq] using h
  have h0 : HasSum (fun i=>(c i)^2) (‖F‖^2) := hparse F
  have hL : HasSum (fun i=>(angularEigenvalue i)^2*(c i)^2) (‖L‖^2) := by
    have h := hparse L
    simpa only [L,F,c,negativeLaplacianAngularC2_coefficient,mul_pow] using h
  have hb (i : AngularIndex) : nativeAngularWeightedSquare 2 F i ≤
      2*((c i)^2+(angularEigenvalue i)^2*(c i)^2) := by
    unfold nativeAngularWeightedSquare
    rw [Real.rpow_two,mul_pow,angularEnergyWeight_sq]
    change ((1+angularEigenvalue i)^2)*(c i)^2 ≤ _
    nlinarith only [sq_nonneg ((angularEigenvalue i-1)*c i)]
  have hm := (h0.summable.add hL.summable).mul_left 2
  have hs : NativeAngularSpectralRegular 2 F :=
    Summable.of_nonneg_of_le (fun _=>sq_nonneg _) hb hm
  refine ⟨hs,?_⟩
  have h := Summable.tsum_le_tsum hb hs hm
  simpa only [tsum_mul_left,h0.summable.tsum_add hL.summable,h0.tsum_eq,hL.tsum_eq] using h

theorem angular_C2_three_halves_trace (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 2 f) :
    NativeAngularSpectralRegular (3/2) (continuousAngularL2 f hf.continuous) ∧
      (∑'i,nativeAngularWeightedSquare (3/2) (continuousAngularL2 f hf.continuous) i) ≤
        2*(‖continuousAngularL2 f hf.continuous‖^2+‖negativeLaplacianAngularC2 f hf‖^2) := by
  have h := angular_C2_spectral_energy f hf
  have hm := nativeAngularSpectralRegular_mono (by norm_num : (3/2:ℝ) ≤ 2) h.1
  exact ⟨hm.1,hm.2.trans h.2⟩

#print axioms negativeLaplacianAngularC2_coefficient
#print axioms angular_C2_spectral_energy
#print axioms angular_C2_three_halves_trace
end Yamabe3.Analysis.SphereSpectrum
