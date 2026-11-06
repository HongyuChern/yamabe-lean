import Yamabe3.Analysis.NativeC1CompletionEnergy
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateWeakDerivative

/-! The actual completed local coordinate derivative of a C1 native
volume representative is its classical derivative, by weak derivative
uniqueness. No gradient representative is supplied separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis
open UniformElliptic SpherePolar PoincareMT.LeviCivitaData.Dirichlet Poincare.Analysis.Sobolev.Weak
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem C1_coordinateDerivative_memLp
    (e:OpenPartialHomeomorph E M) (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {U:M→ℝ} (hU:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 U) (v:E) :
    MemLp (fun x=>fderiv ℝ (U∘e) x v) 2 (volume.restrict K) := by
  have hF:ContDiffOn ℝ 1 (U∘e) e.source:=
    (hU.comp_contMDiffOn (he.of_le (by simp))).contDiffOn
  have hd:ContinuousOn (fun x=>fderiv ℝ (U∘e) x v) K:=
    ((hF.continuousOn_fderiv_of_isOpen e.open_source (by norm_num)).clm_apply continuousOn_const).mono hKs
  letI:IsFiniteMeasure (volume.restrict K):=⟨by rw [Measure.restrict_apply_univ];exact hK.measure_lt_top⟩
  obtain ⟨C,hC⟩:=hK.exists_bound_of_continuousOn hd
  exact MemLp.of_bound (hd.aestronglyMeasurable hK.measurableSet) C
    ((ae_restrict_mem hK.measurableSet).mono fun x hx=>hC x hx)

theorem localCoordinateDerivative_C1_representative_ae
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K O:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (hOK:O⊆K) (hO:IsOpen O)
    {Ω:Set M} (w:H1Zero g.leviCivitaData Ω)
    {U:M→ℝ} (hU:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 U)
    (hrep:(toL2 g.leviCivitaData Ω w:M→ℝ)=ᵐ[g.volumeMeasure] U) (i:Fin 3) :
    (localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single i 1) w:E→ℝ)=ᵐ[volume.restrict O]
      (fun x=>fderiv ℝ (U∘e) x (EuclideanSpace.single i 1)) := by
  let T:=localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single i 1) w
  have hval:(fun x=>(toL2 g.leviCivitaData Ω w) (e x))=ᵐ[volume.restrict O] U∘e:=
    ae_restrict_of_ae_restrict_of_subset hOK (g.ae_comp_on_compact e he hei hK hKs hrep)
  have hw:HasWeakPartialDeriv i (T:E→ℝ) (U∘e) O:=by
    intro φ hφ hc hs
    have hh:=localCoordinateDerivative_weak e he hei hK hKs hOK hO w i hφ hc hs
    have hv:(∫x in O,(toL2 g.leviCivitaData Ω w) (e x)*fderiv ℝ φ x (EuclideanSpace.single i 1))=
        ∫x in O,(U∘e) x*fderiv ℝ φ x (EuclideanSpace.single i 1):=
      integral_congr_ae (hval.mul (EventuallyEq.refl _ _))
    exact hv.symm.trans hh
  have hF:ContDiffOn ℝ 1 (U∘e) O:=
    ((hU.comp_contMDiffOn (he.of_le (by simp))).contDiffOn).mono (hOK.trans hKs)
  have hd:MemLp (fun x=>fderiv ℝ (U∘e) x (EuclideanSpace.single i 1)) 2 (volume.restrict O):=
    (C1_coordinateDerivative_memLp e he hK hKs hU _).mono_measure (Measure.restrict_mono hOK le_rfl)
  exact HasWeakPartialDeriv.ae_eq hO hw (native_hasWeakPartialDeriv_of_contDiffOn_one hO hF i)
    ((Lp.memLp T).locallyIntegrable (by norm_num)) (hd.locallyIntegrable (by norm_num))

#print axioms C1_coordinateDerivative_memLp
#print axioms localCoordinateDerivative_C1_representative_ae
end Yamabe3.Analysis
