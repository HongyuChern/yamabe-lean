import Yamabe3.Analysis.NativeAngularC2Spectral
import Yamabe3.Analysis.NativeHighModelBoundaryMatching

/-! The actual high-model physical Cauchy construction on the original
C2 value / C1 normal data. The same coupled inverse witness has the
three-halves spectral regularity needed by its genuine H2 collar.
This does not claim the native geometric perturbation is already matched. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology Manifold ContDiff lp RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum Poincare.Geometry.Riemannian.SpaceForm

private theorem high_idem (f : AngularL2) : nativeHighProjection (nativeHighProjection f)=nativeHighProjection f := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply,nativeHighProjection,nativeAngularProjection_coefficient]
  split_ifs <;> rfl

theorem exists_actual_high_physical_cauchy_spectral
    (B W : NativeHighPotential) {ε : ℝ} (hε : 0 < ε)
    (d : AngularH1) (hd : nativeHighEnergyProjectionCLM d=d)
    (hdR : NativeAngularSpectralRegular (3/2) (angularEmbedding d))
    (ℓ : AngularL2) (hℓ : nativeHighProjection ℓ=ℓ)
    (hℓR : NativeAngularSpectralRegular (1/2) ℓ) :
    ∃ (σ : AngularH1) (dout din : AngularL2),
      nativeHighEnergyProjectionCLM σ=σ ∧
      NativeAngularSpectralRegular (3/2) (angularEmbedding σ) ∧
      NativeAngularSpectralRegular (3/2) (angularEmbedding (σ+d)) ∧
      modelExteriorPhysicalCurve B ε (σ+d) 0-modelInteriorPhysicalCurve W ε σ 0=
        radialScale ε • angularEmbedding d ∧
      HasDerivWithinAt (modelExteriorPhysicalCurve B ε (σ+d)) dout (Iic 0) 0 ∧
      HasDerivWithinAt (modelInteriorPhysicalCurve W ε σ) din (Ici 0) 0 ∧
      (8/ε:ℝ) • (dout-din)=ℓ := by
  let n : AngularL2 := (ε/(8*radialScale ε)) • ℓ-(1/2:ℝ) • angularEmbedding d
  have hdh : nativeHighProjection (angularEmbedding d)=angularEmbedding d := by
    rw [←nativeHighEnergyProjectionCLM_embedding,hd]
  have hn : nativeHighProjection n=n := by rw [map_sub,map_smul,hℓ,map_smul,hdh]
  have hnR : NativeAngularSpectralRegular (1/2) n :=
    (nativeAngularSpectralRegular_sub (nativeAngularSpectralRegular_smul hℓR _).1
      (nativeAngularSpectralRegular_smul (nativeAngular_three_halves_to_half _ hdR).1 _).1).1
  obtain ⟨σ,hs,hsd,_,he⟩ := exists_nativeHighCoupled_cauchy_matching B W d hd n hn
  have he' : (B.dtn+W.dtn) σ=n-B.dtn d := by
    rw [map_add] at he
    change B.dtn σ+W.dtn σ=_
    calc
      B.dtn σ+W.dtn σ=(B.dtn σ+B.dtn d+W.dtn σ)-B.dtn d := by abel
      _ = n-B.dtn d := by rw [he]
  have hc := congrArg (nativeHighCoupledDtNInverse B W) he'
  rw [nativeHighCoupledDtNInverse_left,hs] at hc
  have hsR : NativeAngularSpectralRegular (3/2) (angularEmbedding σ) := by
    rw [hc]
    convert (nativeHighCoupled_cauchy_spectral_regular B W d n (1/2) (by convert hdR using 1 <;> norm_num) hnR).1 using 1 <;> norm_num
  have hsdR : NativeAngularSpectralRegular (3/2) (angularEmbedding (σ+d)) := by
    have h := (nativeAngularSpectralRegular_sub hsR (nativeAngularSpectralRegular_smul hdR (-1)).1).1
    simpa only [neg_one_smul,sub_neg_eq_add,map_add] using h
  let dout := radialScale ε • ((1/2:ℝ) • angularEmbedding (σ+d)+B.dtn (σ+d))
  let din := radialScale ε • ((1/2:ℝ) • angularEmbedding σ-W.dtn σ)
  refine ⟨σ,dout,din,hs,hsR,hsdR,?_,modelExteriorPhysicalCurve_derivative B ε _ hsd,
    modelInteriorPhysicalCurve_derivative W ε _ hs,?_⟩
  · simp only [modelExteriorPhysicalCurve,modelInteriorPhysicalCurve,neg_zero,zero_div,
      Real.exp_zero,mul_one,B.curve_zero _ hsd,W.curve_zero _ hs,map_add]
    module
  · have heq : dout-din=radialScale ε • ((1/2:ℝ) • angularEmbedding d+n) := by
      dsimp only [dout,din]
      rw [map_add,←he]
      module
    rw [heq]
    have hcancel : (1/2:ℝ) • angularEmbedding d+n=(ε/(8*radialScale ε)) • ℓ := by dsimp [n];abel
    rw [hcancel,smul_smul,smul_smul]
    have hc : (8/ε:ℝ)*radialScale ε*(ε/(8*radialScale ε))=1 := by
      field_simp [hε.ne',(radialScale_pos ε).ne']
    rw [hc,one_smul]

theorem exists_original_C2_C1_high_physical_matching
    (B W : NativeHighPotential) {ε : ℝ} (hε : 0 < ε)
    (d ℓ : UnitSphere 2 → ℝ)
    (hd : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 2 d)
    (hℓ : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 ℓ) :
    ∃ (b σ : AngularH1) (dout din : AngularL2),
      angularEmbedding b=(radialScale ε)⁻¹ • nativeHighProjection (continuousAngularL2 d hd.continuous) ∧
      nativeHighEnergyProjectionCLM b=b ∧ nativeHighEnergyProjectionCLM σ=σ ∧
      NativeAngularSpectralRegular (3/2) (angularEmbedding b) ∧
      NativeAngularSpectralRegular (3/2) (angularEmbedding σ) ∧
      NativeAngularSpectralRegular (3/2) (angularEmbedding (σ+b)) ∧
      modelExteriorPhysicalCurve B ε (σ+b) 0-modelInteriorPhysicalCurve W ε σ 0=
        nativeHighProjection (continuousAngularL2 d hd.continuous) ∧
      HasDerivWithinAt (modelExteriorPhysicalCurve B ε (σ+b)) dout (Iic 0) 0 ∧
      HasDerivWithinAt (modelInteriorPhysicalCurve W ε σ) din (Ici 0) 0 ∧
      (8/ε:ℝ) • (dout-din)=nativeHighProjection (continuousAngularL2 ℓ hℓ.continuous) := by
  have hdR := (nativeAngularSpectralRegular_smul
    (nativeAngularSpectralRegular_high (angular_C2_three_halves_trace d hd).1).1 (radialScale ε)⁻¹).1
  obtain ⟨b,hb,_⟩ := nativeAngular_three_halves_exists_H1 _ hdR
  have hbR : NativeAngularSpectralRegular (3/2) (angularEmbedding b) := by rwa [hb]
  have hbh : nativeHighEnergyProjectionCLM b=b := by
    apply angularEmbedding_injective
    rw [nativeHighEnergyProjectionCLM_embedding,hb,map_smul,high_idem]
  have hℓR := (nativeAngularSpectralRegular_high (angular_C1_half_trace ℓ hℓ).1).1
  obtain ⟨σ,dout,din,hs,hsR,hsbR,hvalue,hout,hin,hflux⟩ :=
    exists_actual_high_physical_cauchy_spectral B W hε b hbh hbR _ (high_idem _) hℓR
  refine ⟨b,σ,dout,din,hb,hbh,hs,hbR,hsR,hsbR,?_,hout,hin,hflux⟩
  rw [hvalue,hb,smul_smul,mul_inv_cancel₀ (radialScale_pos ε).ne',one_smul]

#print axioms exists_actual_high_physical_cauchy_spectral
#print axioms exists_original_C2_C1_high_physical_matching
end Yamabe3.Analysis.Delaunay
