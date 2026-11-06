import Yamabe3.Analysis.NativeBubbleTailLargeCutoff
import Yamabe3.Analysis.StrictLinearFeedback
import Yamabe3.Analysis.PhysicalBubbleTailSupport
import Yamabe3.Analysis.NativeHomogeneousEnergySpace

/-! Actual global tail-absorbed solution with a prescribed fixed receiving
radius. If the given critical source is zero there, the SAME solution
lands boundedly in the genuine closed homogeneous energy subspace. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def receivingH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] receivingH1Normed
private instance receiving65:Fact (1≤(6/5:ℝ≥0∞)) := ⟨one_le_sixFifths⟩

theorem nativeReceiving_tail_solver_of_gap
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (τ L:ℝ) (hL:0 < L)
    (c N:ℝ) (hc:Real.log (max 128 L)≤c) (hN:0<N)
    (hn:∀(B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
      (hsmall:60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3:ℝ)≤Target.yamabeConstant g),
      ‖closedSixFifthsJacobianSolutionCLM g hY B hB hsmall‖≤N)
    (hgap:∀(B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
      (hsmall:60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3:ℝ)≤Target.yamabeConstant g) (t:ℝ),
      ‖closedSixFifthsJacobianSolutionCLM g hY B hB hsmall‖*
        ‖nativeBubbleTailSourceCLM g hY e he hei hK hKs τ c t‖≤(1/2:ℝ)):
      ∀(B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
        (hsmall:60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g),
      ∀a:ℝ,0 < a → ball (0:E) (a*L)⊆e.source →
      let Ω:=e '' ball (0:E) (a*L)
      ∀(X:Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        (T:X →L[ℝ] Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure),
        (∀x:X,(T x:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]0) →
        ∃R:X →L[ℝ] nativeHomogeneousEnergySpace g B hB Ω,
          ‖R‖ ≤ (2*N)*‖T‖ ∧ ∀x:X,∀η:H1Zero g.leviCivitaData univ,
            closedYamabeJacobianForm g B hB (R x).val η=
              ∫y,(T x y+8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a)) y*
                toL2 g.leviCivitaData univ (R x).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure := by
  intro B hB hsmall a ha hsource
  dsimp only
  intro X _ _ T hT
  let Ω:=e '' ball (0:E) (a*L)
  have hΩ:IsOpen Ω := e.isOpen_image_of_subset_source isOpen_ball hsource
  let A:=closedSixFifthsJacobianSolutionCLM g hY B hB hsmall
  let Q:=nativeBubbleTailSourceCLM g hY e he hei hK hKs τ c (Real.log a)
  have hg:‖A‖*‖Q‖ ≤ (1/2:ℝ) := hgap B hB hsmall (Real.log a)
  let J:=strictFeedbackCLM A Q (q:=(1/2:ℝ≥0)) (by norm_num) hg
  have hJ:‖J‖ ≤ 2*N := by
    have hh:=strictFeedbackCLM_norm A Q (q:=(1/2:ℝ≥0)) (by norm_num) hg
    have he:(1-(1/2:ℝ≥0):ℝ)⁻¹=2 := by norm_num
    exact (hh.trans_eq (by norm_num;ring)).trans
      (mul_le_mul_of_nonneg_left (hn B hB hsmall) (by norm_num))
  let H:=J.comp T
  let qtail:=nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a))
  have hweak (x:X) (η:H1Zero g.leviCivitaData univ):
      closedYamabeJacobianForm g B hB (H x) η=
        ∫y,(T x y+8*(qtail y*toL2 g.leviCivitaData univ (H x) y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure := by
    have heq:A (T x+Q (H x))=H x :=
      strictFeedback_fixed A Q (q:=(1/2:ℝ≥0)) (by norm_num) hg (T x)
    calc
      _ = closedYamabeJacobianForm g B hB (A (T x+Q (H x))) η := by rw [heq]
      _ = ∫y,(T x+Q (H x)) y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure := by
        change closedYamabeJacobianForm g B hB
          (closedYamabeJacobianInverse g hY B hB hsmall (closedSixFifthsForcing g hY (T x+Q (H x)))) η=_
        rw [closedYamabeJacobianInverse_spec,closedSixFifthsForcing_apply]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (T x) (Q (H x)),
          nativeBubbleTailSourceCLM_ae g hY e he hei hK hKs τ c (Real.log a) (H x)] with y hy hQ
        rw [hy]
        change (T x y+Q (H x) y)*_=_
        rw [hQ]
  have hLc:L ≤ Real.exp c := by
    have hmax:0 < max 128 L := lt_of_lt_of_le (by norm_num:(0:ℝ)<128) (le_max_left _ _)
    exact (le_max_right 128 L).trans ((Real.exp_log hmax).symm.trans_le
      (Real.exp_le_exp.mpr hc))
  have hqzero:∀y∈Ω,qtail y=0 :=
    native_physicalBubbleTail_zero_inner e K τ c a ha (mul_le_mul_of_nonneg_left hLc ha.le) hsource
  have hhom (x:X):H x∈nativeHomogeneousEnergySpace g B hB Ω := by
    intro φ hs
    rw [hweak,toL2_coe]
    apply integral_eq_zero_of_ae
    filter_upwards [(ae_restrict_iff' hΩ.measurableSet).mp (hT x),φ.memLp.coeFn_toLp] with y hy hφ
    change (T x y+8*(qtail y*toL2 g.leviCivitaData univ (H x) y))*testToL2 g.leviCivitaData univ φ y=0
    rw [show testToL2 g.leviCivitaData univ φ y=φ y from hφ]
    by_cases hyΩ:y∈Ω
    · rw [hy hyΩ,hqzero y hyΩ]
      simp
    · rw [image_eq_zero_of_notMem_tsupport (fun ht=>hyΩ (hs ht)),mul_zero]
  let R:=H.codRestrict (nativeHomogeneousEnergySpace g B hB Ω) hhom
  refine ⟨R,?_,fun x η=>hweak x η⟩
  apply R.opNorm_le_bound (by positivity)
  intro x
  exact (H.le_opNorm x).trans (mul_le_mul_of_nonneg_right
    ((ContinuousLinearMap.opNorm_comp_le J T).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg T))) (norm_nonneg x))

#print axioms nativeReceiving_tail_solver_of_gap
end Yamabe3.Analysis.SpherePolar
