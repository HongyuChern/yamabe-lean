import Yamabe3.Analysis.SphereAmbientLaplacianJetBound
import Yamabe3.Analysis.NativeAngularC2Spectral

/-! Quantitative native three-halves value-trace budget from the same
ambient two-jet. The radial corrections and actual round area are paid. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace lp
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay Poincare.Geometry.Riemannian.SpaceForm Yamabe3.Analysis.NativeC2Green
private abbrev budgetArea := (roundSphereMetric 2).volumeMeasure
local instance : Fact (Module.finrank ℝ E=2+1):=⟨by simp [E]⟩

theorem continuousAngularL2_norm_sq_le_of_bound (f:S→ℝ) (hf:Continuous f)
    {A:ℝ} (hA:0≤A) (hbound:∀θ,|f θ|≤A) :
    ‖continuousAngularL2 f hf‖^2≤(budgetArea univ).toReal*A^2 := by
  let F:=continuousAngularL2 f hf
  have hi:‖F‖^2=∫θ,(f θ)^2 ∂budgetArea:=by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    change (∫θ,(F θ)*(F θ) ∂budgetArea.restrict univ)=_
    rw [setIntegral_univ]
    apply integral_congr_ae
    filter_upwards [continuousAngularL2_ae f hf] with θ hθ
    change (F θ)*(F θ)=(f θ)^2
    rw [show F θ=f θ from hθ]
    ring
  rw [hi]
  calc
    _ ≤ ∫_θ:S,A^2 ∂budgetArea:=integral_mono
      ((hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const _) (fun θ=>by
        simpa only [sq_abs,Pi.pow_apply] using (sq_le_sq₀ (abs_nonneg (f θ)) hA).mpr (hbound θ))
    _ = _:=by simp only [integral_const,smul_eq_mul,measureReal_def]

theorem angular_three_halves_budget_of_ambient_jets {f:E→ℝ}
    (hf:∀θ:S,ContDiffAt ℝ ∞ f (θ:E)) {A:ℝ} (hA:0≤A)
    (hj:∀j≤2,∀θ:S,‖iteratedFDeriv ℝ j f (θ:E)‖≤A) :
    ∃hfs:ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 2 (fun θ:S=>f θ),
      NativeAngularSpectralRegular (3/2) (continuousAngularL2 (fun θ:S=>f θ) hfs.continuous) ∧
      (∑'i,nativeAngularWeightedSquare (3/2) (continuousAngularL2 (fun θ:S=>f θ) hfs.continuous) i)≤
        74*(budgetArea univ).toReal*A^2 := by
  have hfs:ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 2 (fun θ:S=>f θ):=by
    intro θ
    have hc:ContDiffAt ℝ 2 f (θ:E):=(hf θ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    exact hc.contMDiffAt.comp θ contMDiff_coe_sphere.contMDiffAt
  have hs:=angular_C2_three_halves_trace (fun θ:S=>f θ) hfs
  have hv:‖continuousAngularL2 (fun θ:S=>f θ) hfs.continuous‖^2≤(budgetArea univ).toReal*A^2:=
    continuousAngularL2_norm_sq_le_of_bound _ hfs.continuous hA (fun θ=>by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hj 0 (by norm_num) θ)
  have hL:∀θ:S,|-(sphereD.laplacian (fun θ:S=>f θ) θ)|≤6*A:=by
    intro θ
    rw [abs_neg]
    exact sphere_laplacian_bound_of_ambient_two_jets θ (hf θ) hA (fun j hn=>hj j hn θ)
  have hLn:‖negativeLaplacianAngularC2 (fun θ:S=>f θ) hfs‖^2≤(budgetArea univ).toReal*(6*A)^2:=
    continuousAngularL2_norm_sq_le_of_bound _ (continuous_laplacian_C2 _ hfs).neg (by positivity) hL
  refine ⟨hfs,hs.1,hs.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (add_le_add hv hLn) (by norm_num:(0:ℝ)≤2)).trans_eq (by ring)

#print axioms continuousAngularL2_norm_sq_le_of_bound
#print axioms angular_three_halves_budget_of_ambient_jets
end Yamabe3.Analysis.SpherePolar
