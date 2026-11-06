import Yamabe3.Analysis.NativeC1CoordinateDerivative
import Yamabe3.Analysis.NativeRestrictedGradientEnergy

/-! The actual restricted completed gradient energy, expressed through
its proved local coordinate derivative and the retained metric density.
Continuity extends the literal smooth identity; no gradient identification
is assumed for a completed field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis
open SpherePolar PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

def nativeCoordinateEnergyCoefficient (g:RiemannianMetric 3 M)
    (e:OpenPartialHomeomorph E M) (φ:M→ℝ) (j:Fin 3) (x:E):ℝ:=
  ∑i:Fin 3,divergenceCoefficients g e x i j*fderiv ℝ (φ∘e) x (EuclideanSpace.single i 1)

private theorem coefficient_memLp
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {S:Set E} (hS:IsCompact S) (hSs:S⊆e.source)
    (φ:EnergyTest g.leviCivitaData univ) (j:Fin 3) :
    MemLp (nativeCoordinateEnergyCoefficient g e φ j) 2 (volume.restrict S) := by
  have hc:ContinuousOn (nativeCoordinateEnergyCoefficient g e φ j) S:=by
    apply continuousOn_finsetSum
    intro i _
    exact ((contDiffOn_divergenceCoefficients (g:=g) e he hei i j).continuousOn.mono hSs).mul
      ((((φ.smooth.comp_contMDiffOn he).contDiffOn.continuousOn_fderiv_of_isOpen e.open_source (by simp)).clm_apply
        continuousOn_const).mono hSs)
  letI:IsFiniteMeasure (volume.restrict S):=⟨by rw [Measure.restrict_apply_univ];exact hS.measure_lt_top⟩
  obtain ⟨C,hC⟩:=hS.exists_bound_of_continuousOn hc
  exact MemLp.of_bound (hc.aestronglyMeasurable hS.measurableSet) C
    ((ae_restrict_mem hS.measurableSet).mono fun x hx=>hC x hx)

def nativeCoordinateEnergyCoefficientL2
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {S:Set E} (hS:IsCompact S) (hSs:S⊆e.source)
    (φ:EnergyTest g.leviCivitaData univ) (j:Fin 3) : Lp ℝ 2 (volume.restrict S):=
  (coefficient_memLp g e he hei hS hSs φ j).toLp _

theorem nativeRestrictedGradientEnergy_compact_coordinates
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K S:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (hS:IsCompact S) (hSK:S⊆K)
    (w:H1Zero g.leviCivitaData univ) (φ:EnergyTest g.leviCivitaData univ) :
    nativeRestrictedGradientEnergy g (e '' S) w (φ:H1Zero g.leviCivitaData univ)=
      ∑j:Fin 3,inner ℝ (nativeCoordinateEnergyCoefficientL2 g e he hei hS (hSK.trans hKs) φ j)
        (localCoordinateDerivative e he hei hK hKs hSK (EuclideanSpace.single j 1) w) := by
  induction w using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih w =>
    rw [nativeRestrictedGradientEnergy_coe]
    rw [integral_compact_image_eq_pullback_density (g:=g) e he hei hS (hSK.trans hKs)
      (g.leviCivitaData.continuous_inner_gradient w.smooth φ.smooth).measurable]
    let Z (j:Fin 3):=nativeCoordinateEnergyCoefficientL2 g e he hei hS (hSK.trans hKs) φ j
    let Q (j:Fin 3):=localCoordinateDerivative e he hei hK hKs hSK (EuclideanSpace.single j 1)
      (w:H1Zero g.leviCivitaData univ)
    have hinner (j:Fin 3):inner ℝ (Z j) (Q j)=∫x in S,Z j x*Q j x:=by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Eventually.of_forall fun x=>by simp only [real_inner_comm,real_inner_self_eq_norm_sq,Real.inner_apply,mul_comm]
    change _=∑j:Fin 3,inner ℝ (Z j) (Q j)
    rw [show (∑j:Fin 3,inner ℝ (Z j) (Q j))=(∫x in S,∑j:Fin 3,Z j x*Q j x) by
      simp only [hinner];exact (integral_finsetSum _ (fun j _=>(Lp.memLp (Z j)).integrable_mul (Lp.memLp (Q j)))).symm]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS.measurableSet,
      eventually_all.mpr (fun j=>(coefficient_memLp g e he hei hS (hSK.trans hKs) φ j).coeFn_toLp),
      eventually_all.mpr (fun j=>localCoordinateDerivative_coe_ae e he hei hK hKs hSK (EuclideanSpace.single j 1) w)]
      with x hx hz ht
    rw [mul_comm,density_mul_inner_gradient_eq_sum_divergenceCoefficients e he hei w φ (hKs (hSK hx))]
    have hZ(j:Fin 3):Z j x=nativeCoordinateEnergyCoefficient g e φ j x:=hz j
    have hT(j:Fin 3):Q j x=fderiv ℝ (fun y=>w (e y)) x (EuclideanSpace.single j 1):=ht j
    simp only [hZ,hT,nativeCoordinateEnergyCoefficient,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Function.comp_def]
    ring

#print axioms nativeRestrictedGradientEnergy_compact_coordinates
end Yamabe3.Analysis
