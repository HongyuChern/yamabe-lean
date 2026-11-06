import Yamabe3.Analysis.NativePoissonTailIdentity
import Yamabe3.Analysis.NativeShiftedEntranceH2

/-! One original Poisson field on every scale, with a true H2 value and
weak jets. The entrance reflection and tail decomposition overlap and
represent the same field. The boundary energy is explicitly retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)

def nativePoissonAllScaleValue (s : ℝ) (b : AngularH1) : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  if s ≤ 2 then nativeShiftedEntranceValue P s b else nativePoissonTailValue P hplus s b
def nativePoissonAllScaleFirst (s : ℝ) (b : AngularH1) (j : Fin 3) : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  if s ≤ 2 then nativeShiftedEntranceFirst P s b j else nativePoissonTailFirst P hplus s b j
def nativePoissonAllScaleSecond (s : ℝ) (b : AngularH1) (k j : Fin 3) : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  if s ≤ 2 then nativeShiftedEntranceSecond P s b k j else nativePoissonTailSecond P hplus s b k j

def nativePoissonBoundaryEnergy (b : AngularH1) : ℝ :=
  ‖b‖^2+(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)

theorem nativePoissonBoundaryEnergy_nonneg (b : AngularH1) : 0 ≤ nativePoissonBoundaryEnergy b :=
  add_nonneg (sq_nonneg _) (tsum_nonneg (fun i => sq_nonneg _))

 theorem nativePoissonAllScale_H2_same_jets (s : ℝ) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    MemWkp 2 2 (nativePoissonAllScaleValue P hplus s b) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativePoissonAllScaleFirst P hplus s b j)
        (nativePoissonAllScaleValue P hplus s b) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativePoissonAllScaleSecond P hplus s b k j)
        (nativePoissonAllScaleFirst P hplus s b j) nativePoissonEntranceCollar) := by
  by_cases hs : s ≤ 2
  · simpa only [nativePoissonAllScaleValue,nativePoissonAllScaleFirst,nativePoissonAllScaleSecond,if_pos hs] using
      nativeShiftedEntrance_H2_same_jets P s hs b hb
  · simpa only [nativePoissonAllScaleValue,nativePoissonAllScaleFirst,nativePoissonAllScaleSecond,if_neg hs] using
      nativePoissonTail_H2_same_jets P hplus s (by linarith : 1 ≤ s) b

 theorem nativePoissonAllScaleValue_same_field (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativePoissonReflectedCurve P b t : S → ℝ)) (s : ℝ) :
    (nativePoissonAllScaleValue P hplus s b : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  by_cases hs : s ≤ 2
  · rw [nativePoissonAllScaleValue,if_pos hs]
    exact nativeShiftedEntranceValue_same_field P s hs b hb hw hae
  · rw [nativePoissonAllScaleValue,if_neg hs]
    apply nativePoissonTailValue_same_field P hplus b hw _ s (by linarith)
    intro t ht
    simpa only [nativePoissonReflectedCurve,if_pos ht] using hae t

private theorem combine_square_bound {n a d E S N : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hN : 0 ≤ N) (hS : 0 ≤ S)
    (hE : E=N+S) (hn : 0 ≤ n) :
    (n^2 ≤ a*S ∨ n ≤ d*Real.sqrt N) → n^2 ≤ (a+d^2)*E := by
  intro h
  rcases h with h | h
  · rw [hE]
    nlinarith [mul_nonneg ha hN,mul_nonneg (sq_nonneg d) hN,mul_nonneg (sq_nonneg d) hS]
  · have hb := sq_le_sq₀ hn (mul_nonneg hd (Real.sqrt_nonneg N)) |>.2 h
    rw [mul_pow,Real.sq_sqrt hN] at hb
    rw [hE]
    nlinarith [mul_nonneg ha hN,mul_nonneg ha hS,mul_nonneg (sq_nonneg d) hS]

 theorem exists_uniform_nativePoissonAllScale_H2_bounds :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0 ≤ C ∧ 0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (b : AngularH1),NativeAngularSpectralRegular (3/2) (angularEmbedding b) → ∀ s : ℝ,
        ‖nativePoissonAllScaleValue P hplus s b‖^2 ≤ C*nativePoissonBoundaryEnergy b ∧
        (∀ j,‖nativePoissonAllScaleFirst P hplus s b j‖^2 ≤ G*nativePoissonBoundaryEnergy b) ∧
        (∀ k j,‖nativePoissonAllScaleSecond P hplus s b k j‖^2 ≤ K k*nativePoissonBoundaryEnergy b) := by
  obtain ⟨C,G,K,hC,hG,hK,he⟩ := exists_uniform_nativeShiftedEntrance_H2_bounds P
  obtain ⟨D,H,L,hD,hH,hL,ht⟩ := exists_uniform_nativePoissonTail_H2_bounds P hplus
  refine ⟨C+D^2,G+H^2,fun k => K k+(L k)^2,by positivity,by positivity,
    fun k => add_nonneg (hK k) (sq_nonneg _),?_⟩
  intro b hb s
  have hE : nativePoissonBoundaryEnergy b=‖b‖^2+(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := rfl
  have hS : 0 ≤ (∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := tsum_nonneg (fun i => sq_nonneg _)
  have hsqrt : Real.sqrt (‖b‖^2)=‖b‖ := Real.sqrt_sq (norm_nonneg _)
  by_cases hs : s ≤ 2
  · have h := he s hs b hb
    simp only [nativePoissonAllScaleValue,nativePoissonAllScaleFirst,nativePoissonAllScaleSecond,if_pos hs]
    exact ⟨combine_square_bound hC hD (sq_nonneg _) hS hE (norm_nonneg _) (Or.inl h.1),
      fun j => combine_square_bound hG hH (sq_nonneg _) hS hE (norm_nonneg _) (Or.inl (h.2.1 j)),
      fun k j => combine_square_bound (hK k) (hL k) (sq_nonneg _) hS hE (norm_nonneg _) (Or.inl (h.2.2 k j))⟩
  · have h := ht s (by linarith) b
    simp only [nativePoissonAllScaleValue,nativePoissonAllScaleFirst,nativePoissonAllScaleSecond,if_neg hs]
    exact ⟨combine_square_bound hC hD (sq_nonneg _) hS hE (norm_nonneg _) (Or.inr (hsqrt.symm ▸ h.1)),
      fun j => combine_square_bound hG hH (sq_nonneg _) hS hE (norm_nonneg _) (Or.inr (hsqrt.symm ▸ h.2.1 j)),
      fun k j => combine_square_bound (hK k) (hL k) (sq_nonneg _) hS hE (norm_nonneg _) (Or.inr (hsqrt.symm ▸ h.2.2 k j))⟩

#print axioms nativePoissonAllScale_H2_same_jets
#print axioms nativePoissonAllScaleValue_same_field
#print axioms exists_uniform_nativePoissonAllScale_H2_bounds
end Yamabe3.Analysis.SpherePolar
