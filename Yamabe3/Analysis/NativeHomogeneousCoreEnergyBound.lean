import Yamabe3.Analysis.RegularLowH4CoreEnergy
import Yamabe3.Analysis.NativeCoreCutoffEnergyIdentity
import Yamabe3.Analysis.NativeHomogeneousH4Return
import Yamabe3.Analysis.NativeScaledCutoffGeometry

/-! A uniformly bounded core multiplier on the ACTUAL native
homogeneous energy space. The genuine regular-low/H4 return pays
a^(-1/2), the SAME-field compact H1 lift pays sqrt(a), and these costs
cancel exactly. No global a^(-1) smooth-multiplier bound is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def homogeneousCoreNormed (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] homogeneousCoreNormed

theorem native_sqrt_exp_log_cancel {a:ℝ} (ha:0 < a) :
    Real.sqrt a*Real.exp (-Real.log a/2)=1 := by
  have hs:Real.sqrt a=Real.exp (Real.log a/2):=by rw [Real.exp_half,Real.exp_log ha]
  rw [hs,←Real.exp_add,show Real.log a/2+-Real.log a/2=0 by ring,Real.exp_zero]

theorem exists_nativeHomogeneous_uniform_core_energy
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0 < R₀) (hsource:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆ball (0:E) 3)
    (h1:∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1)) :
    ∃δ C:ℝ,0 < δ ∧ 0 ≤ C ∧ ∀a:ℝ,∀ha:0 < a,a ≤ δ →
      ∃ha1:a ≤ 1,∃hfit:euclideanDilatedDomain a (ball (0:E) 3)⊆e.source,
      ∃hΩ:IsOpen (e '' ball (0:E) (a*64)),
      ∃Q:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)) →L[ℝ] H1Zero g.leviCivitaData univ,
        ‖Q‖ ≤ C ∧ ∀W,
          Q W=let Ψ:=nativeChartScaledCutoffTest g e hei ha χ hχ hc (ball (0:E) 3) hs hfit
          energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) Ψ Ψ.smooth W.val := by
  obtain ⟨d,D,hd,hD,hret⟩:=exists_nativeHomogeneous_H4_return g hY gE e he hei hR₀ hsource hcoeff hB hρ
  let LE:=regularLowH4CoreEnergyCLM χ hχ hc hs h1
  have hChart:=nativeWeakChartBound_pos g e he hei (isCompact_closedBall (0:E) R₀) hsource
  let C:=nativeWeakChartBound g e he hei (isCompact_closedBall (0:E) R₀) hsource*‖LE‖*D
  have hC:0 ≤ C:=by dsimp only [C];positivity
  let δ:=min 1 (min (R₀/128) (d/32))
  have hδ:0 < δ:=by dsimp only [δ];positivity
  refine ⟨δ,C,hδ,hC,fun a ha had=>?_⟩
  have ha1:a ≤ 1:=had.trans (min_le_left _ _)
  have ha128:a*128 ≤ R₀:=(le_div_iff₀ (by norm_num:(0:ℝ) < 128)).mp
    (had.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have had32:a*32 ≤ d:=(le_div_iff₀ (by norm_num:(0:ℝ) < 32)).mp
    (had.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have h64:a*64 ≤ R₀:=by linarith
  have h3:a*3 ≤ R₀:=by linarith
  have hfitK:euclideanDilatedDomain a (ball (0:E) 3)⊆closedBall (0:E) R₀:=
    euclideanDilatedBall_subset_closedBall ha h3
  have hfit:euclideanDilatedDomain a (ball (0:E) 3)⊆e.source:=hfitK.trans hsource
  have hsrc64:ball (0:E) (a*64)⊆e.source:=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall h64).trans hsource)
  let Ω:=e '' ball (0:E) (a*64)
  have hΩ:IsOpen Ω:=e.isOpen_image_of_subset_source isOpen_ball hsrc64
  have hRfit:a*Real.exp (Real.log 128)/2 ≤ R₀:=by rw [Real.exp_log (by norm_num:(0:ℝ) < 128)];linarith
  have hRscale:a*Real.exp (Real.log 128)/8 < d:=by rw [Real.exp_log (by norm_num:(0:ℝ) < 128)];linarith
  have hdomain:a*Real.exp (Real.log 128)/2=a*64:=by rw [Real.exp_log (by norm_num:(0:ℝ) < 128)];ring
  have hretA:=hret (Real.log 128) a le_rfl ha hRfit hRscale (fun _:M=>0) contMDiff_const
  dsimp only at hretA
  rw [hdomain] at hretA
  obtain ⟨J,hJ,hJv⟩:=hretA hΩ (fun _ _=>rfl)
  let A:=nativeEuclideanCompletedChartScaleCLM g e he hei (isCompact_closedBall (0:E) R₀) hsource ha ha1
    (ball (0:E) 3) hfitK
  let Q:=A.comp (LE.comp J)
  have hbound:‖Q‖ ≤ C:=by
    apply Q.opNorm_le_bound hC
    intro W
    have hA:=A.le_of_opNorm_le
      (nativeEuclideanCompletedChartScaleCLM_norm g e he hei (isCompact_closedBall (0:E) R₀) hsource ha ha1
        (ball (0:E) 3) hfitK) (LE (J W))
    have hLE:‖LE (J W)‖ ≤ ‖LE‖*((D*Real.exp (-Real.log a/2))*‖W‖):=
      (LE.le_opNorm _).trans (mul_le_mul_of_nonneg_left (J.le_of_opNorm_le hJ W) (norm_nonneg LE))
    apply (hA.trans (mul_le_mul_of_nonneg_left hLE (by positivity))).trans_eq
    calc
      _=(nativeWeakChartBound g e he hei (isCompact_closedBall (0:E) R₀) hsource*‖LE‖*D*‖W‖)*
          (Real.sqrt a*Real.exp (-Real.log a/2)):=by ring
      _=C*‖W‖:=by rw [native_sqrt_exp_log_cancel ha,mul_one]
  have hImage:e '' euclideanDilatedDomain a (ball (0:E) 3)⊆Ω:=
    image_mono ((euclideanDilatedBall_subset_closedBall ha (le_refl (a*3))).trans
      (closedBall_subset_ball (by nlinarith: a*3 < a*64)))
  refine ⟨ha1,hfit,hΩ,Q,hbound,fun W=>?_⟩
  apply nativeCoreCutoff_completed_identity g e he hei (isCompact_closedBall (0:E) R₀) hsource ha ha1
    (ball (0:E) 3) χ hχ hc hs hfitK Ω hΩ hImage (LE (J W)) (regularLowH4Field (J W))
    (regularLowH4CoreEnergyCLM_ae χ hχ hc hs h1 (J W)) W.val
    (nativeHomogeneousEnergyRepresentative g (fun _:M=>0) contMDiff_const hΩ W)
    (nativeHomogeneousEnergyRepresentative_spec g (fun _:M=>0) contMDiff_const hΩ W).2.1
  intro x hx
  exact hJv W ((closedBall_subset_closedBall (by norm_num:(3:ℝ) ≤ 4)) (ball_subset_closedBall (hs hx)))

#print axioms native_sqrt_exp_log_cancel
#print axioms exists_nativeHomogeneous_uniform_core_energy
end Yamabe3.Analysis.SpherePolar
