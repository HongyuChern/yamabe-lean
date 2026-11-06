import Yamabe3.Analysis.NativeDomainEnergyDirichlet
import Yamabe3.Analysis.NativeWeakPhysicalConormal

/-!
# A genuine native forced Dirichlet producer for the physical conormal data

The domain inverse constructs a correction from the actual prescribed L2
source and an arbitrary H1 lifting. Membership of the resulting pair in the
native weak data space is proved, not assumed. The background smallness is
explicit; the zero background specializes to the positive Yamabe operator.
No Euclidean half-end field is asserted to solve this different operator.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory UniformSpace PoincareMT
open scoped Manifold ContDiff InnerProductSpace Topology
namespace Yamabe3.Analysis
open PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

def nativeJacobianPotential (g : RiemannianMetric 3 M) (b : M → ℝ) : M → ℝ :=
  fun x => g.leviCivitaData.scalarCurvature x - 30 * b x ^ 4

theorem nativeJacobianPotential_smooth (g : RiemannianMetric 3 M)
    {b : M → ℝ} (hb : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ b) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (nativeJacobianPotential g b) :=
  g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul (hb.pow 4))

theorem nativeJacobianForm_eq_elliptic (g : RiemannianMetric 3 M)
    (b : M → ℝ) (hb : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ b)
    (v w : H1Zero g.leviCivitaData univ) :
    closedYamabeJacobianForm g b hb v w =
      8 * gradientEnergy g.leviCivitaData univ v w +
      potentialForm g.leviCivitaData univ (by simpa using isCompact_univ)
        (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb) v w := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih v =>
    induction w using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih w =>
      have hp : Integrable (fun x => nativeJacobianPotential g b x * v x * w x)
          g.volumeMeasure := by
        simpa only [EnergyTest.mulSmooth_apply] using
          (v.mulSmooth (nativeJacobianPotential g b)
            (nativeJacobianPotential_smooth g hb)).integrable_mul w
      rw [closedYamabeJacobianForm_coe, gradientEnergy_coe, potentialForm_coe,
        ← integral_const_mul, ← integral_add ((v.integrable_gradient w).const_mul 8) hp]
      rfl

variable (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
  (b : M → ℝ) (hb : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ b)
  (hsmall : 60 * (∫ x, |b x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
    Target.yamabeConstant g)

def nativeForcedDirichletCorrection
    (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure) :
    H1Zero g.leviCivitaData Ω :=
  domainYamabeJacobianInverse g hY Ω b hb hsmall
    ((nativeRestrictedL2SourceOperator g Ω F).comp (nativeDomainEnergyInclusion g Ω) +
      nativeEnergyDirichletForcing g Ω b hb ell)

def nativeForcedDirichletSolution
    (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure) :
    H1Zero g.leviCivitaData univ :=
  ell + nativeDomainEnergyInclusion g Ω
    (nativeForcedDirichletCorrection g hY Ω b hb hsmall ell F)

theorem nativeForcedDirichletSolution_variational
    (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure)
    (η : H1Zero g.leviCivitaData Ω) :
    closedYamabeJacobianForm g b hb
      (nativeForcedDirichletSolution g hY Ω b hb hsmall ell F)
      (nativeDomainEnergyInclusion g Ω η) =
        ∫ x in Ω, F x * toL2 g.leviCivitaData Ω η x ∂g.volumeMeasure := by
  have h := domainYamabeJacobianInverse_spec g hY Ω b hb hsmall
    ((nativeRestrictedL2SourceOperator g Ω F).comp (nativeDomainEnergyInclusion g Ω) +
      nativeEnergyDirichletForcing g Ω b hb ell) η
  change closedYamabeJacobianForm g b hb (nativeDomainEnergyInclusion g Ω
    (nativeForcedDirichletCorrection g hY Ω b hb hsmall ell F))
      (nativeDomainEnergyInclusion g Ω η) =
      nativeRestrictedL2SourceOperator g Ω F (nativeDomainEnergyInclusion g Ω η) -
        closedYamabeJacobianForm g b hb ell (nativeDomainEnergyInclusion g Ω η) at h
  rw [nativeForcedDirichletSolution, map_add, ContinuousLinearMap.add_apply, h]
  rw [nativeRestrictedL2SourceOperator_apply, nativeDomainEnergyInclusion_toL2]
  ring

theorem nativeForcedDirichletSolution_mem_data
    (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure) :
    (nativeForcedDirichletSolution g hY Ω b hb hsmall ell F, F) ∈
      NativeWeakEllipticDataSpace g Ω (nativeJacobianPotential g b)
        (nativeJacobianPotential_smooth g hb) := by
  rw [mem_NativeWeakEllipticDataSpace_iff]
  intro η
  rw [← nativeJacobianForm_eq_elliptic]
  exact nativeForcedDirichletSolution_variational g hY Ω b hb hsmall ell F η

/-- The same produced pair is a genuine data element, with the same source F. -/
def nativeForcedDirichletData
    (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure) :
    NativeWeakEllipticDataSpace g Ω (nativeJacobianPotential g b)
      (nativeJacobianPotential_smooth g hb) :=
  ⟨(nativeForcedDirichletSolution g hY Ω b hb hsmall ell F, F),
    nativeForcedDirichletSolution_mem_data g hY Ω b hb hsmall ell F⟩

theorem nativeForcedDirichletSolution_ae_outside
    (hΩ : MeasurableSet Ω) (ell : H1Zero g.leviCivitaData univ)
    (F : Lp ℝ 2 g.volumeMeasure) :
    ∀ᵐ x ∂g.volumeMeasure, x ∉ Ω →
      toL2 g.leviCivitaData univ
        (nativeForcedDirichletSolution g hY Ω b hb hsmall ell F) x =
      toL2 g.leviCivitaData univ ell x := by
  simp only [nativeForcedDirichletSolution, map_add, nativeDomainEnergyInclusion_toL2]
  filter_upwards [Lp.coeFn_add (toL2 g.leviCivitaData univ ell)
    (toL2 g.leviCivitaData Ω (nativeForcedDirichletCorrection g hY Ω b hb hsmall ell F)),
    toL2_ae_zero_outside hΩ (nativeForcedDirichletCorrection g hY Ω b hb hsmall ell F)]
    with x hadd hz
  intro hx
  rw [hadd, Pi.add_apply, hz hx, add_zero]

theorem nativeForcedDirichletCorrection_unique
    (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure)
    (q : H1Zero g.leviCivitaData Ω)
    (hq : ∀ η : H1Zero g.leviCivitaData Ω,
      closedYamabeJacobianForm g b hb (ell + nativeDomainEnergyInclusion g Ω q)
        (nativeDomainEnergyInclusion g Ω η) =
        ∫ x in Ω, F x * toL2 g.leviCivitaData Ω η x ∂g.volumeMeasure) :
    q = nativeForcedDirichletCorrection g hY Ω b hb hsmall ell F := by
  apply domainYamabeJacobianInverse_unique g hY Ω b hb hsmall
  intro η
  change closedYamabeJacobianForm g b hb (nativeDomainEnergyInclusion g Ω q)
    (nativeDomainEnergyInclusion g Ω η) =
    nativeRestrictedL2SourceOperator g Ω F (nativeDomainEnergyInclusion g Ω η) -
      closedYamabeJacobianForm g b hb ell (nativeDomainEnergyInclusion g Ω η)
  rw [nativeRestrictedL2SourceOperator_apply, nativeDomainEnergyInclusion_toL2]
  have h := hq η
  rw [map_add, ContinuousLinearMap.add_apply] at h
  linarith only [h]

set_option quotPrecheck false
section PhysicalExterior
open SpherePolar NativeChartSphereMetric Metric
variable (gE : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E M)
  (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
  {a C : ℝ} (ha : 0 < a)
  (hs : closedBall (0 : E) (2 * a) ⊆ e.source)
  (hcoeff : ∀ x ∈ closedBall (0 : E) (2 * a),
    gE.euclideanCoefficients x = g.pullbackCoefficients e x)
  (hC : 0 ≤ C)
  (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (a • (θ : E)) ≤ C)

include hs in
private theorem forcedExterior_annulus_source :
    sphereTraceAnnulus a (2 * a) ⊆ e.source := by
  intro x hx
  exact hs (by simpa only [mem_closedBall, dist_zero_right] using hx.2)

local notation "T" => nativePhysicalSphereTraceCLM g gE e he hei ha
  (show a < 2 * a from by linarith only [ha])
  (show a ∈ Icc a (2 * a) from ⟨le_rfl, by linarith only [ha]⟩)
  (forcedExterior_annulus_source e hs) hC
  (fun θ => hcoeff _ (by
    rw [mem_closedBall, dist_zero_right, EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le]
    linarith only [ha]))
  (fun θ => hGauss (a • (θ : E))) hρ
local notation "Oext" => (e '' closedBall (0 : E) a)ᶜ
set_option quotPrecheck false

/-- The correction is in H1-zero of the actual exterior, so it changes no
physical value trace. This is not restriction of a volume AE equality. -/
theorem nativeForcedDirichletSolution_preserves_physical_trace
    (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure) :
    T (nativeForcedDirichletSolution g hY Oext b hb hsmall ell F) = T ell := by
  unfold nativeForcedDirichletSolution
  rw [map_add]
  have hz := nativePhysicalSphereTraceCLM_domainInclusion_zero g gE e he hei ha
    (show a < 2 * a from by linarith only [ha])
    (show a ∈ Icc a (2 * a) from ⟨le_rfl, by linarith only [ha]⟩)
    (forcedExterior_annulus_source e hs) hC
    (fun θ => hcoeff _ (by
      rw [mem_closedBall, dist_zero_right, EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le]
      linarith only [ha]))
    (fun θ => hGauss (a • (θ : E))) hρ Oext
    (fun θ hx => hx ⟨a • (θ : E), by
      rw [mem_closedBall, dist_zero_right, EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le], rfl⟩)
    (nativeForcedDirichletCorrection g hY Oext b hb hsmall ell F)
  exact (congrArg (fun v => T ell + v) hz).trans (add_zero _)

include hY hsmall in
/-- A real producer of the previously conditional exterior weak data. -/
theorem exists_native_forced_exterior_data
    (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure) :
    ∃ d : NativeWeakEllipticDataSpace g Oext (nativeJacobianPotential g b)
      (nativeJacobianPotential_smooth g hb),
      d.val.2 = F ∧ T d.val.1 = T ell := by
  refine ⟨nativeForcedDirichletData g hY Oext b hb hsmall ell F, rfl, ?_⟩
  exact nativeForcedDirichletSolution_preserves_physical_trace g hY b hb hsmall
    gE e he hei hGauss ha hs hcoeff hC hρ ell F

include hY hsmall in
/-- The same constructed data simultaneously retain the prescribed source,
physical value trace, and physical weak conormal Green functional. -/
theorem exists_native_forced_exterior_data_with_conormal
    (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure) :
    ∃ d : NativeWeakEllipticDataSpace g Oext (nativeJacobianPotential g b)
      (nativeJacobianPotential_smooth g hb),
      d.val.2 = F ∧ T d.val.1 = T ell ∧
      ∀ v : H1Zero g.leviCivitaData univ,
        nativeRestrictedEllipticForm g Oext (nativeJacobianPotential g b)
          (nativeJacobianPotential_smooth g hb) d.val.1 v -
        (∫ x in Oext, F x * toL2 g.leviCivitaData univ v x ∂g.volumeMeasure) =
        EuclideanSphereTrace.nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs
          hcoeff hC hρ (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb)
          d (HilbertTraceQuotient.quotientMap T v) := by
  obtain ⟨d, hF, hT⟩ := exists_native_forced_exterior_data g hY b hb hsmall
    gE e he hei hGauss ha hs hcoeff hC hρ ell F
  refine ⟨d, hF, hT, fun v => ?_⟩
  have h := EuclideanSphereTrace.nativeWeakPhysicalConormal_quotientMap g gE e he hei
    hGauss ha hs hcoeff hC hρ (nativeJacobianPotential g b)
    (nativeJacobianPotential_smooth g hb) d v
  simpa only [nativeWeakEnergySourceDataCLM_apply, nativeRestrictedL2SourceOperator_apply,
    hF] using h.symm

include hY in
/-- At zero background the original Yamabe positivity is sufficient;
no spectral gap, inverse or critical-smallness hypothesis is added. -/
theorem exists_native_conformal_exterior_data
    (ell : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure) :
    ∃ d : NativeWeakEllipticDataSpace g Oext g.leviCivitaData.scalarCurvature
      g.leviCivitaData.contMDiff_scalarCurvature,
      d.val.2 = F ∧ T d.val.1 = T ell := by
  have hzero : 60 * (∫ x : M, |(0 : ℝ)| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g := by simpa using hY.le
  have hp : nativeJacobianPotential g (fun _ : M => (0 : ℝ)) =
      g.leviCivitaData.scalarCurvature := by
    funext x
    simp only [nativeJacobianPotential, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, sub_zero]
  obtain ⟨d, hF, hT⟩ := exists_native_forced_exterior_data g hY
    (fun _ : M => (0 : ℝ)) contMDiff_const hzero
    gE e he hei hGauss ha hs hcoeff hC hρ ell F
  have hd : d.val ∈ NativeWeakEllipticDataSpace g Oext
      g.leviCivitaData.scalarCurvature g.leviCivitaData.contMDiff_scalarCurvature := by
    simpa only [hp] using d.property
  exact ⟨⟨d.val, hd⟩, hF, hT⟩

end PhysicalExterior
end Yamabe3.Analysis
