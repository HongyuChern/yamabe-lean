import Yamabe3.Analysis.NativeOuterLargeTailReceiver
import Yamabe3.Analysis.NativeReceiverSmallScaleJets
import Yamabe3.Analysis.NativeHomogeneousReceiverBallH4

/-! The SAME inner smooth return controls actual entrance-scale H4
and all two-jets, when the already constructed inner tail radius leaves
room around the entrance. No additional representative is chosen. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Elliptic.InteriorEstimates
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem exists_nativeInnerReturn_entrance_bound
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hB : gE.euclideanCoefficients 0=innerSL ℝ) (hρ : gE.pullbackVolumeDensity id 0=1) :
    ∃δ : ℝ, 0 < δ ∧ ∃C : ℝ≥0∞, C ≠ ⊤ ∧ ∀(c a : ℝ),
      Real.log 32 ≤ c → 0 < a → a*Real.exp c/8 < δ →
      closedBall (0 : E) (a*Real.exp c/2) ⊆ e.source →
      (∀x∈closedBall (0 : E) (a*Real.exp c/2),gE.euclideanCoefficients x=g.pullbackCoefficients e x) →
      ∀U : M → ℝ, ContMDiffOn (𝓡 3) 𝓘(ℝ,ℝ) ∞ U (e '' ball (0 : E) (a*Real.exp c/2)) →
      (∀x∈ball (0 : E) (a*Real.exp c/2),
        -8*g.leviCivitaData.laplacian U (e x)+g.leviCivitaData.scalarCurvature (e x)*U (e x)=0) →
      ∀A : ℝ≥0∞, derivativeProfile 2 (ball (0 : E) 1) 4 (fun z => U (e ((a*Real.exp c/8) • z))) ≤ A →
        (∀j≤2,∀x∈closedBall (0 : E) 2,
          ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun z => U (e (a • z))) x‖ ≤ C*A) ∧
          derivativeProfile 2 (ball (0 : E) 1) 4 (fun z => U (e (a • z))) ≤ C*A := by
  obtain ⟨J,hJ,hjets⟩ := exists_nativeReceiver_entrance_two_jet_bound (M := M)
  obtain ⟨δ,D,hδ,hD,hball⟩ := exists_nativeHomogeneous_receiver_ball_H4_bound g gE e he hei hB hρ
  let v : ℝ≥0∞ := (volume (ball (0 : E) 2))^(1/2 : ℝ)
  have hv : v ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  let K : ℝ≥0∞ := ENNReal.ofReal D*v
  refine ⟨δ,hδ,(1+K)*ENNReal.ofReal J,by finiteness,fun c a hc ha hscale hsource hcoeff U hU hP A hA => ?_⟩
  have hec : 32 ≤ Real.exp c := by
    exact (Real.exp_log (by norm_num : (0 : ℝ) < 32)).symm.trans_le (Real.exp_le_exp.mpr hc)
  have hapos : 0 < a*Real.exp c := mul_pos ha (Real.exp_pos _)
  have hbig : 8 < Real.exp c := lt_of_lt_of_le (by norm_num) hec
  have har : a < a*Real.exp c/8 := by nlinarith [mul_pos ha (sub_pos.mpr hbig)]
  have haδ : a < δ := har.trans hscale
  have hR : 0 < a*Real.exp c/2 := by positivity
  have h3 : a*3 < a*Real.exp c/2 := by nlinarith [mul_pos ha (sub_pos.mpr hbig)]
  have hs : -c ≤ Real.log (1/32 : ℝ) := by
    simpa only [one_div,Real.log_inv] using neg_le_neg hc
  have hjet : ∀j≤2,∀x∈closedBall (0 : E) 2,
      ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun z => U (e (a • z))) x‖ ≤ ENNReal.ofReal J*A := by
    intro j hj x hx
    have hh := hjets e he a (-c) ha hs
      (by simpa only [neg_neg] using ball_subset_closedBall.trans hsource) U
      (by simpa only [neg_neg] using hU) j hj x hx
    simp only [neg_neg] at hh
    exact hh.trans (mul_le_mul le_rfl hA zero_le zero_le)
  have hΩ : IsOpen (e '' ball (0 : E) (a*Real.exp c/2)) :=
    e.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsource)
  have hus : ∀x∈ball (0 : E) (a*Real.exp c/2),ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) ∞ U (e x) :=
    fun x hx => hU.contMDiffAt (hΩ.mem_nhds (mem_image_of_mem e hx))
  have hest := hball (a*Real.exp c/2) hR hsource hcoeff a ha haδ h3 U hus hP
  have hpt : ∀ᵐx : E ∂volume.restrict (ball (0 : E) 2), ‖U (e (a • x))‖ₑ ≤ ENNReal.ofReal J*A := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hh := hjet 0 (by norm_num) x (ball_subset_closedBall hx)
    simpa only [norm_iteratedFDeriv_zero,ofReal_norm] using hh
  have hn := eLpNorm_le_of_ae_enorm_bound (p := 2) hpt
  simp only [Measure.restrict_apply_univ,ENNReal.toReal_ofNat] at hn
  have hjC : ENNReal.ofReal J ≤ (1+K)*ENNReal.ofReal J := by
    rw [add_mul,one_mul]
    exact le_add_of_nonneg_right zero_le
  have hkC : K*ENNReal.ofReal J ≤ (1+K)*ENNReal.ofReal J := by
    rw [add_mul,one_mul]
    exact le_add_of_nonneg_left zero_le
  refine ⟨fun j hj x hx => (hjet j hj x hx).trans (mul_le_mul hjC le_rfl zero_le zero_le),?_⟩
  apply hest.trans
  apply (mul_le_mul le_rfl hn zero_le zero_le).trans
  have hh : ENNReal.ofReal D*((ENNReal.ofReal J*A)*v)=(K*ENNReal.ofReal J)*A := by
    dsimp only [K]
    ring
  simpa only [smul_eq_mul,v,one_div,mul_assoc] using hh.le.trans (mul_le_mul hkC le_rfl zero_le zero_le)

#print axioms exists_nativeInnerReturn_entrance_bound
end Yamabe3.Analysis.SpherePolar
