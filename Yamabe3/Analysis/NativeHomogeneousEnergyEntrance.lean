import Yamabe3.Analysis.NativeHomogeneousEnergyRepresentative
import Yamabe3.Analysis.NativeInnerReturnEntrance

/-! A proved quantitative entrance estimate for EVERY element of the
same complete homogeneous energy space and its fixed regular representative.
This supplies the actual a^(-1/2) cost for subsequent source/trace factories. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Elliptic.InteriorEstimates PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def homogeneousEntranceH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] homogeneousEntranceH1Normed

theorem exists_nativeHomogeneousEnergy_entrance_bound
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hsource : closedBall (0 : E) R₀ ⊆ e.source)
    (hcoeff : ∀x∈closedBall (0 : E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB : gE.euclideanCoefficients 0=innerSL ℝ) (hρ : gE.pullbackVolumeDensity id 0=1) :
    ∃δ : ℝ, 0 < δ ∧ ∃C : ℝ≥0∞, C ≠ ⊤ ∧ ∀(c a : ℝ),
      Real.log 32 ≤ c → 0 < a → a*Real.exp c/2 ≤ R₀ → a*Real.exp c/8 < δ →
      ∀(B : M → ℝ) (hBs : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B),
      let Ω := e '' ball (0 : E) (a*Real.exp c/2)
      ∀hΩ : IsOpen Ω, (∀x∈Ω,B x=0) →
      ∀W : nativeHomogeneousEnergySpace g B hBs Ω,
      let U := nativeHomogeneousEnergyRepresentative g B hBs hΩ W
      (∀j≤2,∀x∈closedBall (0 : E) 2,
        ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun z => U (e (a • z))) x‖ ≤
          C*ENNReal.ofReal (Real.exp (-Real.log a/2))*ENNReal.ofReal ‖W‖) ∧
      derivativeProfile 2 (ball (0 : E) 1) 4 (fun z => U (e (a • z))) ≤
        C*ENNReal.ofReal (Real.exp (-Real.log a/2))*ENNReal.ofReal ‖W‖ := by
  obtain ⟨δ₁,hδ₁,D,hD,hrcv⟩ := exists_nativeCritical_receiver_H4_bound g hY gE e he hei hR₀ hsource hcoeff hB hρ
  obtain ⟨δ₂,hδ₂,J,hJ,hentry⟩ := exists_nativeInnerReturn_entrance_bound g gE e he hei hB hρ
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,J*D,by finiteness,fun c a hc ha hfit hscale B hBs => ?_⟩
  dsimp only
  intro hΩ hzero W
  let Ω := e '' ball (0 : E) (a*Real.exp c/2)
  let U := nativeHomogeneousEnergyRepresentative g B hBs hΩ W
  have hU := nativeHomogeneousEnergyRepresentative_spec g B hBs hΩ W
  have hapos : 0 < a*Real.exp c := mul_pos ha (Real.exp_pos _)
  have hR : 0 < a*Real.exp c/2 := by positivity
  have hsrc : closedBall (0 : E) (a*Real.exp c/2) ⊆ e.source :=
    (closedBall_subset_closedBall hfit).trans hsource
  have hco : ∀x∈closedBall (0 : E) (a*Real.exp c/2),gE.euclideanCoefficients x=g.pullbackCoefficients e x :=
    fun x hx => hcoeff x (closedBall_subset_closedBall hfit hx)
  have hPe : ∀x∈ball (0 : E) (a*Real.exp c/2),
      -8*g.leviCivitaData.laplacian U (e x)+g.leviCivitaData.scalarCurvature (e x)*U (e x)=0 := by
    intro x hx
    have hh := hU.2.2 (e x) (mem_image_of_mem e hx)
    simpa only [hzero _ (mem_image_of_mem e hx),zero_pow (by decide : 4≠0),mul_zero,sub_zero] using hh
  have hH4 := hrcv (a*Real.exp c/2) hR hfit W.val Ω hΩ U hU.1 hU.2.1
    (fun x hx => mem_image_of_mem e hx) hPe (a*Real.exp c/8) (by positivity)
    (hscale.trans_le (min_le_left _ _)) (by linarith only [hapos])
  have hec : 32 ≤ Real.exp c :=
    (Real.exp_log (by norm_num : (0 : ℝ) < 32)).symm.trans_le (Real.exp_le_exp.mpr hc)
  have har : a ≤ a*Real.exp c/8 := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hec)]
  have hlog : Real.log a ≤ Real.log (a*Real.exp c/8) := Real.log_le_log ha har
  have he : ENNReal.ofReal (Real.exp (-Real.log (a*Real.exp c/8)/2)) ≤
      ENNReal.ofReal (Real.exp (-Real.log a/2)) := ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (by linarith only [hlog]))
  have hH4' : derivativeProfile 2 (ball (0 : E) 1) 4 (fun z => U (e ((a*Real.exp c/8) • z))) ≤
      D*ENNReal.ofReal (Real.exp (-Real.log a/2))*ENNReal.ofReal ‖W‖ :=
    hH4.trans (mul_le_mul (mul_le_mul le_rfl he zero_le zero_le) le_rfl zero_le zero_le)
  have hh := hentry c a hc ha (hscale.trans_le (min_le_right _ _)) hsrc hco U hU.1 hPe _ hH4'
  exact ⟨fun j hj x hx => (hh.1 j hj x hx).trans_eq (by ring),hh.2.trans_eq (by ring)⟩

#print axioms exists_nativeHomogeneousEnergy_entrance_bound
end Yamabe3.Analysis.SpherePolar
