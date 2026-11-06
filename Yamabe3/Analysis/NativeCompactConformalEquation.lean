import Yamabe3.Analysis.NativeCompactConformalSource

/-! The literal full conformal equation of the SAME compact closed H2 jet.
The equation is proved on actual C2 generators by Green's identity, then
extended through continuous L2 pairings. It is not an input to the closure. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix

def nativeConformalDensityTest (g:RiemannianMetric 3 E) (φ:E→ℝ) (x:E) : ℝ :=
  g.pullbackVolumeDensity id x*(-8*g.leviCivitaData.laplacian φ x+g.leviCivitaData.scalarCurvature x*φ x)

theorem nativeConformalDensityTest_memLp (g:RiemannianMetric 3 E)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) :
    MemLp (nativeConformalDensityTest g φ) 2 volume := by
  have hΔ:=g.leviCivitaData.hasCompactSupport_laplacian hc
  have hR:HasCompactSupport (fun x=>g.leviCivitaData.scalarCurvature x*φ x):=hc.mul_left
  have h8:HasCompactSupport (fun x=>(-8:ℝ)*g.leviCivitaData.laplacian φ x):=hΔ.mul_left
  have hcont:Continuous (nativeConformalDensityTest g φ):=
    (native_density_smooth_positive g).1.continuous.mul
      ((continuous_const.mul (g.leviCivitaData.contMDiff_laplacian hφ.contMDiff).continuous).add
        (g.leviCivitaData.contMDiff_scalarCurvature.continuous.mul hφ.continuous))
  exact hcont.memLp_of_hasCompactSupport (h8.add hR).mul_left

theorem nativeCompactConformalEquation_pairing (g:RiemannianMetric 3 E)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆nativePoissonEntranceCollar)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hφc:HasCompactSupport φ)
    (J:nativeCollarJetClosure) :
    inner ℝ ((nativeConformalDensityTest_memLp g φ hφ hφc).toLp (nativeConformalDensityTest g φ))
        (nativeCompactCollarValueCLM χ hχ J)=
      inner ℝ ((hφ.continuous.memLp_of_hasCompactSupport hφc).toLp φ)
        (nativeCompactConformalSourceCLM g χ hχ J) := by
  let htest:=nativeConformalDensityTest_memLp g φ hφ hφc
  let hφ2:MemLp φ 2 volume:=hφ.continuous.memLp_of_hasCompactSupport hφc
  let A:=(innerSL ℝ (htest.toLp (nativeConformalDensityTest g φ))).comp (nativeCompactCollarValueCLM χ hχ)
  let B:=(innerSL ℝ (hφ2.toLp φ)).comp (nativeCompactConformalSourceCLM g χ hχ)
  have hclosed:=isClosed_eq A.continuous B.continuous
  change A J=B J
  refine nativeC2CollarJetInclusion_dense.induction_on J hclosed ?_
  intro u
  change inner ℝ (htest.toLp (nativeConformalDensityTest g φ))
      (nativeCompactCollarValueCLM χ hχ (nativeC2CollarJetInclusion u))=
    inner ℝ (hφ2.toLp φ) (nativeCompactConformalSourceCLM g χ hχ (nativeC2CollarJetInclusion u))
  rw [L2.inner_def,L2.inner_def]
  calc
    _ = ∫x,(nativeC2Cutoff χ hχ u).val x*(nativeConformalDensityTest g φ x) := by
      apply integral_congr_ae
      filter_upwards [htest.coeFn_toLp,nativeCompactConformalValue_C2_ae hχ hs u] with x ht hu
      simp only [Real.inner_apply,ht,hu,mul_comm]
    _ = ∫x,(nativeC2Cutoff χ hχ u).val x*
        (-8*g.leviCivitaData.laplacian φ x+g.leviCivitaData.scalarCurvature x*φ x) ∂g.volumeMeasure := by
      rw [native_integral_eq_density]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x=>by unfold nativeConformalDensityTest;ring)
    _ = ∫x,(-8*g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x+
        g.leviCivitaData.scalarCurvature x*(nativeC2Cutoff χ hχ u).val x)*φ x ∂g.volumeMeasure :=
      nativeC2Cutoff_conformal_transposed g hχ hc hs u φ hφ hφc
    _ = _ := by
      rw [native_integral_eq_density]
      apply integral_congr_ae
      filter_upwards [hφ2.coeFn_toLp,nativeCompactConformalSource_C2_ae g hχ hs u] with x ht hu
      simp only [Real.inner_apply,ht,hu]
      ring

theorem nativeCompactConformalEquation_integral (g:RiemannianMetric 3 E)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆nativePoissonEntranceCollar)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hφc:HasCompactSupport φ)
    (J:nativeCollarJetClosure) :
    (∫x,(nativeCompactCollarValueCLM χ hχ J:E→ℝ) x*nativeConformalDensityTest g φ x)=
      ∫x,(nativeCompactConformalSourceCLM g χ hχ J:E→ℝ) x*φ x := by
  have hh:=nativeCompactConformalEquation_pairing g χ hχ hc hs φ hφ hφc J
  rw [L2.inner_def,L2.inner_def] at hh
  calc
    _ = ∫x,inner ℝ (((nativeConformalDensityTest_memLp g φ hφ hφc).toLp (nativeConformalDensityTest g φ):E→ℝ) x)
        ((nativeCompactCollarValueCLM χ hχ J:E→ℝ) x) := by
      apply integral_congr_ae
      filter_upwards [(nativeConformalDensityTest_memLp g φ hφ hφc).coeFn_toLp] with x hx
      simp only [Real.inner_apply,hx,mul_comm]
    _ = _ := hh
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(hφ.continuous.memLp_of_hasCompactSupport hφc (p:=2)).coeFn_toLp] with x hx
      simp only [Real.inner_apply,hx,mul_comm]

#print axioms nativeConformalDensityTest_memLp
#print axioms nativeCompactConformalEquation_pairing
#print axioms nativeCompactConformalEquation_integral
end Yamabe3.Analysis.SpherePolar
