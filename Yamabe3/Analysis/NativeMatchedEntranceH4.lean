import Yamabe3.Analysis.NativeUnitSphereTransmissionNeighborhood
import Yamabe3.Analysis.NativeCollarMatchedSourceAssembly
import Yamabe3.Analysis.NativeCollarPhysicalSourceBound
import Yamabe3.Analysis.NativeMatchedCollarH2Bound

/-! The original matched physical equations yield a genuine one-sided
H4 extension at every unit-sphere point. Geometry, neighborhoods, a linear
extension and its bound precede all source and solution inputs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Delaunay
open Poincare.Analysis.Sobolev.Euclidean

 theorem exists_nativeMatched_entrance_H4 {D : Set E} (hD : IsOpen D)
    (hDc : D⊆nativePoissonEntranceCollar)
    (g : RiemannianMetric 3 E) (r : ℝ) (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ)
    (V : ℝ →ᵇ ℝ) (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t))
    (a : E) (ha : ‖a‖=1) (haD : a∈D) :
    ∃ (N W : Set E) (L : (E → ℝ) →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞),
      a∈N ∧ IsOpen N ∧ IsCompact (closure N) ∧ closure N⊆D ∧
      IsOpen W ∧ IsCompact (closure W) ∧ closure W⊆D ∧ C≠⊤ ∧
      ∀ (J K : nativeCollarJetClosure) (u f q : E → ℝ),
        nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K →
        nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K →
        ((J.val.1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u) →
        (∀ U : Set E,IsOpen U → IsCompact (closure U) → closure U⊆(ball (0:E) 1\{(0:E)}) →
          nativeWeakRescaledDelaunayJacobian U g r v phase u=ᵐ[volume.restrict U] f) →
        ((nativeExteriorNativeJacobianCLM g r V K.val : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar] q) →
        MemWkp 2 2 f W → MemWkp 2 2 q W →
        MemWkp 4 2 (L (nativeCollarGluedFunction J.val.1 K.val.1)) N ∧
        iteratedWeakSobolevNorm 4 2 (L (nativeCollarGluedFunction J.val.1 K.val.1)) N≤
          C*(iteratedWeakSobolevNorm 2 2 f W+iteratedWeakSobolevNorm 2 2 q W+
            (ENNReal.ofReal ‖J‖+ENNReal.ofReal ‖K‖)) ∧
        EqOn (L (nativeCollarGluedFunction J.val.1 K.val.1)) (J.val.1 : E → ℝ) (N∩ball (0:E) 1) := by
  classical
  obtain ⟨N,W,L,H,haN,hN,hNc,hND,hW,hWc,hWD,hH,hreg⟩ :=
    exists_unitSphere_transmission_neighborhood (nativeRescaledMetric g r) hD a ha haD
  have hWC := hWD.trans hDc
  obtain ⟨G,hG,hglue⟩ := exists_nativeCollarGlued_H2_bound hW hWc hWC
  obtain ⟨P,hP,hpos⟩ := exists_nativeCollar_potential_source_bound hW hWc hWC
    _ (nativeInnerDivergencePotential_smooth g r v hv phase)
  obtain ⟨Q,hQ,hneg⟩ := exists_nativeCollar_potential_source_bound hW hWc hWC
    _ (nativeExteriorDivergencePotential_smooth g r V hVs)
  refine ⟨N,W,L,H*(G+(1+P)+(1+Q)),haN,hN,hNc,hND,hW,hWc,hWD,by finiteness,?_⟩
  intro J K u f q hvalue hnormal hJu hi ho hf hq
  have hq8 : MemWkp 2 2 (fun x => q x/8) W := by
    simpa only [div_eq_mul_inv,mul_comm] using MemWkp.const_smul (by norm_num : (1:ℝ≥0∞)≤2) hW hq (8:ℝ)⁻¹
  have hnq8 : iteratedWeakSobolevNorm 2 2 (fun x => q x/8) W≤ iteratedWeakSobolevNorm 2 2 q W := by
    calc
      _ = ENNReal.ofReal ((8:ℝ)⁻¹)*iteratedWeakSobolevNorm 2 2 q W := by
        simpa only [div_eq_mul_inv,mul_comm,
          Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤(8:ℝ)⁻¹)] using
          wkpNorm_const_smul (by norm_num : (1:ℝ≥0∞)≤2) hW hq (8:ℝ)⁻¹
      _ ≤ _ := mul_le_of_le_one_left zero_le (by norm_num)
  have hp := hpos J f hf
  have hn := hneg K (fun x => q x/8) hq8
  have hs := nativeCollarGluedFunction_original_sources g r v phase V J K hvalue hnormal hJu hi ho hW hWc hWC
  have hr := hreg _ _ _ ((nativeCollarGluedFunction_local_H2 J K hvalue hnormal).restrict hD hDc) hp.1 hn.1 hs.2
  let Z := iteratedWeakSobolevNorm 2 2 f W+iteratedWeakSobolevNorm 2 2 q W+
    (ENNReal.ofReal ‖J‖+ENNReal.ofReal ‖K‖)
  have hF : iteratedWeakSobolevNorm 2 2 f W≤Z :=
    (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
  have hQn : iteratedWeakSobolevNorm 2 2 q W≤Z :=
    (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)
  have hJK : ENNReal.ofReal ‖J‖+ENNReal.ofReal ‖K‖≤Z := le_add_of_nonneg_left zero_le
  have hJ : ENNReal.ofReal ‖J‖≤Z := (le_add_of_nonneg_right zero_le).trans hJK
  have hK : ENNReal.ofReal ‖K‖≤Z := (le_add_of_nonneg_left zero_le).trans hJK
  have hgB := (hglue J K hvalue hnormal).2.trans (mul_le_mul le_rfl hJK zero_le zero_le)
  have hpB : iteratedWeakSobolevNorm 2 2
      (fun x => f x-(annularDelaunayPotential v phase x+nativeDelaunayPotentialError g r v phase x)*(J.val.1 : E → ℝ) x) W≤(1+P)*Z :=
    hp.2.trans ((add_le_add hF (mul_le_mul le_rfl hJ zero_le zero_le)).trans_eq (by ring))
  have hnB : iteratedWeakSobolevNorm 2 2
      (fun x => q x/8-nativeExteriorDivergencePotential g r V x*(K.val.1 : E → ℝ) x) W≤(1+Q)*Z :=
    hn.2.trans ((add_le_add (hnq8.trans hQn) (mul_le_mul le_rfl hK zero_le zero_le)).trans_eq (by ring))
  refine ⟨hr.1,?_,?_⟩
  · exact hr.2.1.trans ((mul_le_mul le_rfl (add_le_add hgB (add_le_add hpB hnB)) zero_le zero_le).trans_eq (by dsimp [Z];ring))
  · intro x hx
    exact (hr.2.2 hx).trans (by simp only [nativeCollarGluedFunction,piecewise_eq_of_mem _ _ _ hx.2])

#print axioms exists_nativeMatched_entrance_H4
end Yamabe3.Analysis.SpherePolar
