import Yamabe3.Analysis.NativeCompactCoordinateEnergy

/-! Restriction consistency and the actual restricted energy of a completed
field with a C1 representative. The local derivative is identified by its
proved weak derivative, never supplied as an additional hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis
open SpherePolar PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

private theorem derivative_restrict_ae
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K S:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (hSK:S⊆K)
    {Ω:Set M} (w:H1Zero g.leviCivitaData Ω) (v:E) :
    (localCoordinateDerivative e he hei hK hKs hSK v w:E→ℝ)=ᵐ[volume.restrict S]
      (coordinateDerivative e he hei hK hKs v w:E→ℝ) := by
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (c:=1) (by simp)
    (by simpa only [one_smul] using Measure.restrict_mono hSK (le_refl volume)) _

theorem localCoordinateDerivative_C1_representative_restrict_ae
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K O S:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (hOK:O⊆K) (hO:IsOpen O) (hSO:S⊆O)
    {Ω:Set M} (w:H1Zero g.leviCivitaData Ω)
    {U:M→ℝ} (hU:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 U)
    (hrep:(toL2 g.leviCivitaData Ω w:M→ℝ)=ᵐ[g.volumeMeasure] U) (i:Fin 3) :
    (localCoordinateDerivative e he hei hK hKs (hSO.trans hOK) (EuclideanSpace.single i 1) w:E→ℝ)
      =ᵐ[volume.restrict S] (fun x=>fderiv ℝ (U∘e) x (EuclideanSpace.single i 1)) := by
  have ho:=localCoordinateDerivative_C1_representative_ae g e he hei hK hKs hOK hO w hU hrep i
  exact (derivative_restrict_ae g e he hei hK hKs (hSO.trans hOK) w _).trans
    (ae_restrict_of_ae_restrict_of_subset hSO
      ((derivative_restrict_ae g e he hei hK hKs hOK w _).symm.trans ho))

private theorem C1_coordinate_gradient
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {U:M→ℝ} (hU:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 U) {x:E} (hx:x∈e.source) (v:E) :
    fderiv ℝ (U∘e) x v=g.inner (e x) (g.leviCivitaData.gradient U (e x)) (mfderiv (𝓡 3) (𝓡 3) e x v) := by
  rw [g.leviCivitaData.inner_gradient]
  have h:=mvfderiv_comp x ((hU (e x)).mdifferentiableAt (by simp))
    ((he.contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp))
  have h':=congrArg (fun L=>L v) h
  simp only [mvfderiv,mfderiv_eq_fderiv,NormedSpace.fromTangentSpace,ContinuousLinearMap.comp_apply] at h'
  convert! h' using 1

theorem C1_density_gradient_coefficients
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {U H:M→ℝ} (hU:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 U) (hH:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 H)
    {x:E} (hx:x∈e.source) :
    g.pullbackVolumeDensity e x*g.inner (e x) (g.leviCivitaData.gradient U (e x)) (g.leviCivitaData.gradient H (e x))=
      ∑i:Fin 3,∑j:Fin 3,divergenceCoefficients g e x i j*fderiv ℝ (U∘e) x (EuclideanSpace.single j 1)*
        fderiv ℝ (H∘e) x (EuclideanSpace.single i 1) := by
  have hD:e.MDifferentiable (𝓡 3) (𝓡 3):=⟨he.mdifferentiableOn (by simp),hei.mdifferentiableOn (by simp)⟩
  have hinv:=g.isInvertible_pullbackCoefficients (hD.mfderiv_injective hx)
  obtain ⟨w,hw⟩:=hD.mfderiv_surjective hx (g.leviCivitaData.gradient U (e x))
  have hF:g.pullbackCoefficients e x w=fderiv ℝ (U∘e) x:=by
    ext v
    rw [C1_coordinate_gradient g e he hU hx]
    change g.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) (mfderiv (𝓡 3) (𝓡 3) e x v)=_
    rw [hw]
  rw [sum_divergenceCoefficients_eq_inverse_pairing,←hF,hinv.inverse_apply_self,
    C1_coordinate_gradient g e he hH hx,hw,g.symm]

variable [CompactSpace M] [ConnectedSpace M]
theorem nativeRestrictedGradientEnergy_C1_representative
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K O S:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (hOK:O⊆K) (hO:IsOpen O)
    (hS:IsCompact S) (hSO:S⊆O)
    (w:H1Zero g.leviCivitaData univ) {U:M→ℝ} (hU:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 U)
    (hrep:(toL2 g.leviCivitaData univ w:M→ℝ)=ᵐ[g.volumeMeasure] U)
    (φ:EnergyTest g.leviCivitaData univ) :
    nativeRestrictedGradientEnergy g (e '' S) w (φ:H1Zero g.leviCivitaData univ)=
      ∫x in e '' S,g.inner x (g.leviCivitaData.gradient U x) (g.leviCivitaData.gradient φ x) ∂g.volumeMeasure := by
  rw [nativeRestrictedGradientEnergy_compact_coordinates g e he hei hK hKs hS (hSO.trans hOK)]
  rw [integral_compact_image_eq_pullback_density (g:=g) e he hei hS (hSO.trans (hOK.trans hKs))
    (NativeC1Green.continuous_inner_gradient_C1 g.leviCivitaData hU (φ.smooth.of_le (by simp))).measurable]
  let Z (j:Fin 3):=nativeCoordinateEnergyCoefficientL2 g e he hei hS (hSO.trans (hOK.trans hKs)) φ j
  let Q (j:Fin 3):=localCoordinateDerivative e he hei hK hKs (hSO.trans hOK) (EuclideanSpace.single j 1) w
  have hinner (j:Fin 3):inner ℝ (Z j) (Q j)=∫x in S,Z j x*Q j x:=by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun x=>by simp only [Real.inner_apply]
  change (∑j:Fin 3,inner ℝ (Z j) (Q j))=_
  simp only [hinner]
  trans ∫x in S,∑j:Fin 3,Z j x*Q j x
  · exact (integral_finsetSum _ (fun j _=>(Lp.memLp (Z j)).integrable_mul (Lp.memLp (Q j)))).symm
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hS.measurableSet,
    eventually_all.mpr (fun j=>(show (Z j:E→ℝ)=ᵐ[volume.restrict S] nativeCoordinateEnergyCoefficient g e φ j from MemLp.coeFn_toLp _)),
    eventually_all.mpr (fun j=>localCoordinateDerivative_C1_representative_restrict_ae
      g e he hei hK hKs hOK hO hSO w hU hrep j)] with x hx hz hq
  have hZ (j:Fin 3):Z j x=nativeCoordinateEnergyCoefficient g e φ j x:=hz j
  have hQ (j:Fin 3):Q j x=fderiv ℝ (U∘e) x (EuclideanSpace.single j 1):=hq j
  rw [mul_comm,C1_density_gradient_coefficients g e he hei hU (φ.smooth.of_le (by simp)) (hKs (hOK (hSO hx)))]
  simp only [hZ,hQ,nativeCoordinateEnergyCoefficient,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms localCoordinateDerivative_C1_representative_restrict_ae
#print axioms C1_density_gradient_coefficients
#print axioms nativeRestrictedGradientEnergy_C1_representative
end Yamabe3.Analysis
