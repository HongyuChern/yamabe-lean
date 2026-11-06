import Yamabe3.Analysis.NativeMatchedDelaunayCollar
import Yamabe3.Analysis.NativeWeakDilation
import PoincareLib.Analysis.Elliptic.Regularity.Iteration.LocalSobolev

/-! The scale representatives are the same physical function. Their
actual H2 regularity transports back to open neighborhoods of every
nonzero physical point, without choosing a different field at each point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

def nativePhysicalScaleWindow (s : ℝ) : Set E :=
  (fun x : E => Real.exp s • x) ⁻¹' nativePoissonEntranceCollar

theorem nativePhysicalScaleWindow_open (s : ℝ) : IsOpen (nativePhysicalScaleWindow s) :=
  (nativePolarTimeWindow_open (1/2)).preimage (continuous_id.const_smul (Real.exp s))

theorem nativePhysicalScaleWindow_off_zero (s : ℝ) : nativePhysicalScaleWindow s⊆({0}ᶜ : Set E) := by
  intro x hx
  change x≠0
  intro he
  have hn := hx.1
  apply hn
  change Real.exp s • x=0
  rw [he,smul_zero]

theorem nativePhysicalScaleWindow_covers {x : E} (hx : x≠0) :
    x∈nativePhysicalScaleWindow (-Real.log ‖x‖) := by
  apply (nativePolarTimeWindow_norm (1/2) _).mpr
  have hn : ‖Real.exp (-Real.log ‖x‖) • x‖=1 := by
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_neg,
      Real.exp_log (norm_pos_iff.mpr hx),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  rw [hn]
  constructor
  · exact Real.exp_lt_one_iff.mpr (by norm_num)
  · exact Real.one_lt_exp_iff.mpr (by norm_num)

theorem native_scaled_H2_to_physical {u : E → ℝ} (s : ℝ)
    (h : MemWkp 2 2 (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x)) nativePoissonEntranceCollar) :
    MemWkp 2 2 u (nativePhysicalScaleWindow s) := by
  have hc := MemWkp.const_smul (by norm_num : (1:ℝ≥0∞)≤2) (nativePolarTimeWindow_open (1/2)) h (Real.exp (-3*s/2))
  have hm := memWkp_comp_dilation (Real.exp_ne_zero s) (nativePolarTimeWindow_open (1/2)) (by norm_num : (1:ℝ≥0∞)≤2) 2 hc
  have he : (fun x : E => Real.exp (-3*s/2)*(Real.exp (3*s/2)*u (Real.exp (-s) • (Real.exp s • x))))=u := by
    funext x
    rw [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul,
      ←mul_assoc,←Real.exp_add]
    rw [show -3*s/2+3*s/2=0 by ring,Real.exp_zero,one_mul]
  rw [he] at hm
  exact hm

theorem native_all_scale_H2_local {u : E → ℝ}
    (h : ∀s : ℝ,MemWkp 2 2 (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x)) nativePoissonEntranceCollar) :
    MemWkpLocally 2 u ({0}ᶜ : Set E) := by
  intro x hx
  exact ⟨nativePhysicalScaleWindow (-Real.log ‖x‖),nativePhysicalScaleWindow_open _,
    nativePhysicalScaleWindow_covers hx,nativePhysicalScaleWindow_off_zero _,native_scaled_H2_to_physical _ (h _)⟩

theorem exists_nativeMatchedDelaunay_same_field_localH2
    {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (B : NativeHighPotential) (p : DelaunayPhaseData κ)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ∃w : ℝ × S → ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) ∧
      ∀s : ℝ,((nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  obtain ⟨w,hw,he⟩ := nativeMatchedDelaunay_same_field hκ0 hκ1 B p hp F
  refine ⟨w,hw,native_all_scale_H2_local (fun s => ?_),he⟩
  exact (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) (he s)).mp
    (nativeMatchedDelaunay_memH2 hκ0 hκ1 B p hp s F)

#print axioms nativePhysicalScaleWindow_covers
#print axioms native_scaled_H2_to_physical
#print axioms native_all_scale_H2_local
#print axioms exists_nativeMatchedDelaunay_same_field_localH2
end Yamabe3.Analysis.SpherePolar
