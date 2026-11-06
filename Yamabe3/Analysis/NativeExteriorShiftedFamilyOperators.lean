import Yamabe3.Analysis.NativeExteriorShiftedFamilyLinearity
import Yamabe3.Analysis.NativeExteriorHalfEndJetBound

/-! A true bounded linear exterior H2 jet producer at every negative
scale. Linearity of ALL actual jets follows from equality of their
value classes and weak-jet uniqueness, not independent derivative input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def nativeExteriorShiftedFamilyJetLinear (P:NativeHighPotential) (T:X →L[ℝ] AngularH1)
    (hT:∀x,NativeAngularSpectralRegular (3/2) (angularEmbedding (T x))) (s:ℝ) :
    X →ₗ[ℝ] nativeCollarJetClosure where
  toFun x:=nativeExteriorShiftedJet P s (T x) (hT x)
  map_add' x y:=by
    apply nativeCollarJet_value_injective
    exact nativeExteriorShiftedFamilyValue_add P T hT s x y
  map_smul' c x:=by
    apply nativeCollarJet_value_injective
    exact nativeExteriorShiftedFamilyValue_smul P T hT s c x

theorem exists_nativeExteriorShiftedFamilyJetCLM
    (P:NativeHighPotential) (T:X →L[ℝ] AngularH1)
    (hT:∀x,NativeAngularSpectralRegular (3/2) (angularEmbedding (T x)))
    (hE:∃D:ℝ,0≤D ∧ ∀x,(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (T x)) i)≤D*‖x‖^2) :
    ∃C:ℝ,0≤C ∧ ∀s:ℝ,s≤0 →
      ∃J:X →L[ℝ] nativeCollarJetClosure,‖J‖≤C ∧
        ∀x,J x=nativeExteriorShiftedJet P s (T x) (hT x) := by
  obtain ⟨C,hC,hb⟩:=exists_nativeExterior_halfEnd_family_bound P (fun x=>T x) hT hE
  refine ⟨C,hC,?_⟩
  intro s hs
  let L:=nativeExteriorShiftedFamilyJetLinear P T hT s
  have hL (x:X):‖L x‖≤C*‖x‖ := hb x s hs
  exact ⟨L.mkContinuous C hL,LinearMap.mkContinuous_norm_le _ hC hL,fun x=>rfl⟩

#print axioms nativeExteriorShiftedFamilyJetLinear
#print axioms exists_nativeExteriorShiftedFamilyJetCLM
end Yamabe3.Analysis.SpherePolar
