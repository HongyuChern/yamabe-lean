import Yamabe3.Analysis.NativeOriginalSourceEntranceBound

/-! A bounded original H2 source and the SAME matched H2 jets give a
one-sided actual H4 entrance extension. The bound precedes the source;
it remains explicitly pointwise in the native metric and physical scale. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay
open Poincare.Analysis.Sobolev.Euclidean

theorem exists_nativeSourceJet_entrance_H4_bound
    (g:RiemannianMetric 3 E) (r:ℝ) (v:ℝ→ℝ) (hv:ContDiff ℝ ∞ v) (phase τ:ℝ)
    {CJ CK:ℝ} (hCJ:0≤CJ) (hCK:0≤CK) (θ:E) (hθ:‖θ‖=1):
    ∃(N:Set E)(L:(E→ℝ)→ₗ[ℝ](E→ℝ))(C:ℝ≥0∞),
      θ∈N ∧ IsOpen N ∧ IsCompact (closure N) ∧ closure N⊆nativePoissonEntranceCollar ∧ C≠⊤ ∧
      ∀(f:HalfEndPhysicalH2SourceGraph)(J K:nativeCollarJetClosure)(u:E→ℝ),
        ‖J‖≤CJ*‖f‖→‖K‖≤CK*‖f‖→
        nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K→
        nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K→
        ((J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]u)→
        (∀U:Set E,IsOpen U→IsCompact (closure U)→closure U⊆ball (0:E) 1\{0}→
          nativeWeakRescaledDelaunayJacobian U g r v phase u=ᵐ[volume.restrict U]
            fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8)→
        ((nativeExteriorNativeJacobianCLM g r (nativePoissonExteriorPotential (fullBubbleHighPotential (-τ))) K.val:E→ℝ)
          =ᵐ[volume.restrict nativeNegativeEntranceCollar](fun _=>0))→
        MemWkp 4 2 (L (nativeCollarGluedFunction J.val.1 K.val.1)) N ∧
        iteratedWeakSobolevNorm 4 2 (L (nativeCollarGluedFunction J.val.1 K.val.1)) N≤C*ENNReal.ofReal ‖f‖ ∧
        (L (nativeCollarGluedFunction J.val.1 K.val.1)=ᵐ[volume.restrict (N∩ball (0:E) 1)]u):=by
  let D:=nativePoissonEntranceCollar∩halfEndSourceAnnulus
  have hD:IsOpen D:=(nativePolarTimeWindow_open (1/2)).inter halfEndSourceAnnulus_isOpen
  have hθ0:θ≠0:=by intro h;rw [h,norm_zero] at hθ;norm_num at hθ
  have hθD:θ∈D:=by
    constructor
    · change θ≠0 ∧ -Real.log ‖θ‖∈Ioo (-(1/2:ℝ)) (1/2)
      norm_num [hθ,hθ0]
    · change (3/4:ℝ)<‖θ‖ ∧ ‖θ‖<3/2
      norm_num [hθ]
  obtain ⟨N,W,L,H,hθN,hN,hNc,hND,hW,hWc,hWD,hH,hreg⟩:=exists_nativeMatched_entrance_H4 hD
    inter_subset_left g r v hv phase _ (nativeBubbleExteriorPotential_smooth τ) θ hθ hθD
  refine ⟨N,L,H*(1+ENNReal.ofReal CJ+ENNReal.ofReal CK),hθN,hN,hNc,hND.trans inter_subset_left,by finiteness,?_⟩
  intro f J K u hJ hK hvalue hnormal hJu hi ho
  have hWS:W⊆halfEndSourceAnnulus:=subset_closure.trans (hWD.trans inter_subset_right)
  have hf:=halfEndH2SourceGraph_normalized_entrance_bound f
  have hfW:=hf.1.mono_set (by norm_num) hW hWS
  have hfN:iteratedWeakSobolevNorm 2 2 (fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8) W≤ENNReal.ofReal ‖f‖:=
    (wkpNorm_mono_set (by norm_num) hW hWS hf.1).trans hf.2
  have hzero:MemWkp 2 2 (fun _:E=>0) W:=MemWkp_zero_fun (by norm_num) hW
  obtain ⟨hr,hn,he⟩:=hreg J K u _ (fun _=>0) hvalue hnormal hJu hi ho hfW hzero
  refine ⟨hr,?_,?_⟩
  · have hJn:ENNReal.ofReal ‖J‖≤ENNReal.ofReal CJ*ENNReal.ofReal ‖f‖:=
      (ENNReal.ofReal_le_ofReal hJ).trans_eq (ENNReal.ofReal_mul hCJ)
    have hKn:ENNReal.ofReal ‖K‖≤ENNReal.ofReal CK*ENNReal.ofReal ‖f‖:=
      (ENNReal.ofReal_le_ofReal hK).trans_eq (ENNReal.ofReal_mul hCK)
    have hz:iteratedWeakSobolevNorm 2 2 (fun _:E=>0) W=0:=wkpNorm_zero_fun_zero (by norm_num) hW
    rw [hz,add_zero] at hn
    exact hn.trans ((mul_le_mul le_rfl (add_le_add hfN (add_le_add hJn hKn)) zero_le zero_le).trans_eq (by ring))
  · have hsub:N∩ball (0:E) 1⊆nativePoissonEntranceCollar:=
      inter_subset_left.trans (subset_closure.trans (hND.trans inter_subset_left))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hJu,
      ae_restrict_mem (hN.inter isOpen_ball).measurableSet] with x hx hxN
    exact (he hxN).trans hx

#print axioms exists_nativeSourceJet_entrance_H4_bound
end Yamabe3.Analysis.SpherePolar
