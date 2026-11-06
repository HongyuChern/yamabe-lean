import Yamabe3.Analysis.NativeMatchedEntranceH4
import Yamabe3.Analysis.NativeH4MatchedCompensationBound

/-! Original H2 graph sources and the computed finite compensation satisfy
all local source premises of the transmission estimate. The same inner
field has an H4 extension with a bound fixed before the original source.
This is still pointwise in the retained metric and scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
set_option maxRecDepth 4096
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
open Poincare.Analysis.Sobolev.Euclidean

 theorem halfEndH2SourceGraph_normalized_entrance_bound (f : HalfEndPhysicalH2SourceGraph) :
    MemWkp 2 2 (fun x => halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8) halfEndSourceAnnulus ∧
    iteratedWeakSobolevNorm 2 2 (fun x => halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8)
      halfEndSourceAnnulus≤ENNReal.ofReal ‖f‖ := by
  have h := halfEndH2SourceGraph_entrance_H2_bound f
  have he : (fun x => halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8)=
      (fun x => (8:ℝ)⁻¹*halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x) := by funext x;ring
  rw [he]
  refine ⟨MemWkp.const_smul (by norm_num) halfEndSourceAnnulus_isOpen h.1 (8:ℝ)⁻¹,?_⟩
  rw [wkpNorm_const_smul (by norm_num) halfEndSourceAnnulus_isOpen h.1,
    Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤(8:ℝ)⁻¹)]
  have h8 : ENNReal.ofReal ((8:ℝ)⁻¹)*(8:ℝ≥0∞)=1 := by
    rw [show (8:ℝ≥0∞)=ENNReal.ofReal (8:ℝ) by norm_num,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤(8:ℝ)⁻¹)]
    norm_num
  have hnum (t : ℝ≥0∞) : ENNReal.ofReal ((8:ℝ)⁻¹)*(8*t)=t := by
    rw [←mul_assoc,h8,one_mul]
  exact (mul_le_mul le_rfl h.2 zero_le zero_le).trans_eq (hnum _)

 theorem exists_nativeOriginal_entrance_H4_bound
    (g : RiemannianMetric 3 E) (r : ℝ) (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ)
    (P : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v₀ : ℝ → ℝ) (hv₀ : Continuous v₀) (hb : ∀t,0≤v₀ t ∧ v₀ t≤1)
    (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (T : HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource)
    (Ji Ko : HalfEndPhysicalH4Graph →L[ℝ] nativeCollarJetClosure)
    (a : E) (ha : ‖a‖=1) :
    ∃ (N : Set E) (L : (E → ℝ) →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞),
      a∈N ∧ IsOpen N ∧ IsCompact (closure N) ∧ closure N⊆nativePoissonEntranceCollar ∧ C≠⊤ ∧
      ∀ (f : HalfEndPhysicalH2SourceGraph) (Y : HalfEndPhysicalH4Graph) (u : E → ℝ),
        nativeCollarValueTraceCLM (Ji Y)=nativeCollarValueTraceCLM (Ko Y) →
        nativeCollarNormalTraceCLM (Ji Y)=nativeCollarNormalTraceCLM (Ko Y) →
        (((Ji Y).val.1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u) →
        (∀U : Set E,IsOpen U → IsCompact (closure U) → closure U⊆(ball (0:E) 1\{(0:E)}) →
          nativeWeakRescaledDelaunayJacobian U g r v phase u=ᵐ[volume.restrict U]
            (fun x => halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8)) →
        ((nativeExteriorNativeJacobianCLM g r (nativePoissonExteriorPotential (fullBubbleHighPotential (-τ))) (Ko Y).val : E → ℝ)
          =ᵐ[volume.restrict nativeNegativeEntranceCollar]
            (fun x => nativeBubbleCollarCompensation τ
              (nativeCauchyCompensationData ht (nativeH4GraphAngularValueCLM Y) (nativeH4GraphAngularNormalCLM Y)) x+
              nativeBubbleCollarCompensation τ (nativeSupportedTwoSidedExteriorCompensation P hp v₀ hv₀ hb b ht (T Y)) x)) →
        MemWkp 4 2 (L (nativeCollarGluedFunction (Ji Y).val.1 (Ko Y).val.1)) N ∧
        iteratedWeakSobolevNorm 4 2 (L (nativeCollarGluedFunction (Ji Y).val.1 (Ko Y).val.1)) N≤
          C*(ENNReal.ofReal ‖f‖+ENNReal.ofReal ‖Y‖) ∧
        (L (nativeCollarGluedFunction (Ji Y).val.1 (Ko Y).val.1)=ᵐ[volume.restrict (N∩ball (0:E) 1)] u) := by
  let D := nativePoissonEntranceCollar∩halfEndSourceAnnulus
  have hD : IsOpen D := (nativePolarTimeWindow_open (1/2)).inter halfEndSourceAnnulus_isOpen
  have ha0 : a≠0 := by intro h;subst a;norm_num at ha
  have haD : a∈D := by
    constructor
    · change a≠0 ∧ -Real.log ‖a‖∈Ioo (-(1/2:ℝ)) (1/2)
      norm_num [ha,ha0]
    · change (3/4:ℝ)<‖a‖ ∧ ‖a‖<3/2
      norm_num [ha]
  obtain ⟨N,W,L,H,haN,hN,hNc,hND,hW,hWc,hWD,hH,hreg⟩ := exists_nativeMatched_entrance_H4 hD
    inter_subset_left g r v hv phase _ (nativeBubbleExteriorPotential_smooth τ) a ha haD
  have hW0 : closure W⊆({0}ᶜ : Set E) := fun x hx => (hWD hx).1.1
  obtain ⟨A,B,hA,hB,hq⟩ := exists_nativeH4Matched_compensation_bound P hp v₀ hv₀ hb b ht 2 hW hWc hW0
  let M := A+B*ENNReal.ofReal ‖T‖+ENNReal.ofReal ‖Ji‖+ENNReal.ofReal ‖Ko‖
  refine ⟨N,L,H*(1+M),haN,hN,hNc,hND.trans inter_subset_left,by dsimp [M];finiteness,?_⟩
  intro f Y u hvalue hnormal hJu hi ho
  have hf := halfEndH2SourceGraph_normalized_entrance_bound f
  have hWS : W⊆halfEndSourceAnnulus := subset_closure.trans (hWD.trans inter_subset_right)
  have hfm := hf.1.mono_set (by norm_num : (1:ℝ≥0∞)≤2) hW hWS
  have hfn := (wkpNorm_mono_set (by norm_num) hW hWS hf.1).trans hf.2
  have hqm := hq T Y
  have hr := hreg (Ji Y) (Ko Y) u _ _ hvalue hnormal hJu hi ho hfm hqm.1
  have hJi : ENNReal.ofReal ‖Ji Y‖≤ENNReal.ofReal ‖Ji‖*ENNReal.ofReal ‖Y‖ := by
    simpa only [ENNReal.ofReal_mul (norm_nonneg Ji)] using ENNReal.ofReal_le_ofReal (Ji.le_opNorm Y)
  have hKo : ENNReal.ofReal ‖Ko Y‖≤ENNReal.ofReal ‖Ko‖*ENNReal.ofReal ‖Y‖ := by
    simpa only [ENNReal.ofReal_mul (norm_nonneg Ko)] using ENNReal.ofReal_le_ofReal (Ko.le_opNorm Y)
  have hnorm := add_le_add (add_le_add hfn hqm.2) (add_le_add hJi hKo)
  have hbudget : ENNReal.ofReal ‖f‖+M*ENNReal.ofReal ‖Y‖≤
      (1+M)*(ENNReal.ofReal ‖f‖+ENNReal.ofReal ‖Y‖) := by
    have hfZ : ENNReal.ofReal ‖f‖≤ENNReal.ofReal ‖f‖+ENNReal.ofReal ‖Y‖ := le_add_of_nonneg_right zero_le
    have hYZ : ENNReal.ofReal ‖Y‖≤ENNReal.ofReal ‖f‖+ENNReal.ofReal ‖Y‖ := le_add_of_nonneg_left zero_le
    exact (add_le_add hfZ (mul_le_mul le_rfl hYZ zero_le zero_le)).trans_eq (by ring)
  refine ⟨hr.1,?_,?_⟩
  · have halg (a b c d e n t : ℝ≥0∞) : (a+(b+c*d)*t)+(e*t+n*t)=a+(b+c*d+e+n)*t := by ring
    have hh := (hnorm.trans_eq (halg _ _ _ _ _ _ _)).trans hbudget
    have hassoc (h m t : ℝ≥0∞) : h*((1+m)*t)=(h*(1+m))*t := (mul_assoc _ _ _).symm
    exact hr.2.1.trans ((mul_le_mul le_rfl hh zero_le zero_le).trans_eq (hassoc _ _ _))
  · have hsub : N∩ball (0:E) 1⊆nativePoissonEntranceCollar :=
      inter_subset_left.trans (subset_closure.trans (hND.trans inter_subset_left))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hJu,
      ae_restrict_mem (hN.inter isOpen_ball).measurableSet] with x hx hxN
    exact (hr.2.2 hxN).trans hx

#print axioms halfEndH2SourceGraph_normalized_entrance_bound
#print axioms exists_nativeOriginal_entrance_H4_bound
end Yamabe3.Analysis.UniformElliptic
