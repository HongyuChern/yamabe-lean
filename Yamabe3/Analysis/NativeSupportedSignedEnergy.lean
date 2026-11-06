import Yamabe3.Analysis.NativeFullBubbleSignedPairing
import Yamabe3.Analysis.NativeFullBubbleNativePotential
import Yamabe3.Analysis.NativeOriginalSignedEnergy

/-! The SAME signed completed element has its actual full-potential
integral identity. All products are L2 at the fixed scale, so integral
subtraction is justified. No uniform bound or extra PDE is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable {g:RiemannianMetric 3 M} {gE:RiemannianMetric 3 E} {e:OpenPartialHomeomorph E M}
  {he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source}
  {hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target}
  {R₀:ℝ} {hsource:closedBall (0:E) R₀⊆e.source}
  {P:NativeHighPotential}
  {hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ}
  {v:ℝ→ℝ} {hv:Continuous v} {hb:∀t,0 ≤ v t ∧ v t ≤ 1}
  {τ cTail:ℝ} {ht:0 < τ} {m n:ℕ} {b S CR CM:ℝ}
  {χin χout:E→ℝ} {hχin:ContDiff ℝ ∞ χin} {hχout:ContDiff ℝ ∞ χout}
  {a:ℝ} {ha:0 < a} {ha1:a ≤ 1}
  (W:NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
    (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
    (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
    (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1)


 def nativeSupportedSignedEnergy
    (Y:nativeSupportedSourcePairSpace b)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))):
    H1Zero g.leviCivitaData univ:=
  W.Q Y.val+energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val-R.val

 theorem nativeSupportedSignedEnergy_ae
    (Y:nativeSupportedSourcePairSpace b)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))):
    (toL2 g.leviCivitaData univ (nativeSupportedSignedEnergy W Y R):M→ℝ)=ᵐ[g.volumeMeasure]
      fun y=>toL2 g.leviCivitaData univ (W.Q Y.val) y-(1-W.core y)*toL2 g.leviCivitaData univ R.val y:=by
  let z:=toL2 g.leviCivitaData univ (W.Q Y.val)
  let m:=toL2 g.leviCivitaData univ
    (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val)
  let r:=toL2 g.leviCivitaData univ R.val
  have hh:toL2 g.leviCivitaData univ (nativeSupportedSignedEnergy W Y R)=z+m-r:=by
    simp only [nativeSupportedSignedEnergy,map_sub,map_add,z,m,r]
  rw [hh]
  filter_upwards [Lp.coeFn_sub (z+m) r,Lp.coeFn_add z m,
    native_energyMulSmooth_toL2_ae g W.core W.core.smooth R.val] with y hs ha hm
  rw [hs]
  simp only [Pi.sub_apply]
  rw [ha]
  simp only [Pi.add_apply]
  change z y+m y-r y=_
  change m y=W.core y*r y at hm
  rw [hm]
  change z y+W.core y*r y-r y=z y-(1-W.core y)*r y
  ring
 theorem nativeSupportedSignedEnergy_full_reaction_integral
    (Y:nativeSupportedSourcePairSpace b)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))) (η:EnergyTest g.leviCivitaData univ):
    let q:=nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a
    (∫y,8*q y*toL2 g.leviCivitaData univ (nativeSupportedSignedEnergy W Y R) y*η y ∂g.volumeMeasure)=
      (∫y,8*q y*toL2 g.leviCivitaData univ (W.Q Y.val) y*η y ∂g.volumeMeasure)-
      (∫y,8*q y*(1-W.core y)*toL2 g.leviCivitaData univ R.val y*η y ∂g.volumeMeasure):=by
  dsimp only
  let q:=nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a
  let Q:=W.Q Y.val
  let Z:=nativeSupportedSignedEnergy W Y R
  have hZ:(toL2 g.leviCivitaData univ Z:M→ℝ)=ᵐ[g.volumeMeasure]
      (fun y=>toL2 g.leviCivitaData univ Q y-(1-W.core y)*toL2 g.leviCivitaData univ R.val y):=
    nativeSupportedSignedEnergy_ae W Y R
  have hqm:MemLp (fun y=>q y*toL2 g.leviCivitaData univ Q y) 2 g.volumeMeasure:=
    nativeFullBubble_product_memLp_two g e (isCompact_closedBall (0:E) R₀) τ a _
  have hzm:MemLp (fun y=>q y*toL2 g.leviCivitaData univ Z y) 2 g.volumeMeasure:=
    nativeFullBubble_product_memLp_two g e (isCompact_closedBall (0:E) R₀) τ a _
  have hrm:MemLp (fun y=>q y*(1-W.core y)*toL2 g.leviCivitaData univ R.val y) 2 g.volumeMeasure:=by
    apply (hqm.sub hzm).ae_eq
    filter_upwards [hZ] with y hz
    dsimp only [Pi.sub_apply]
    linear_combination -q y*hz
  have hiQ:Integrable (fun y=>8*q y*toL2 g.leviCivitaData univ Q y*η y) g.volumeMeasure:=by
    convert (hqm.const_mul 8).integrable_mul η.memLp using 1
    congr 1
    funext y
    simp only [Pi.mul_apply]
    ring
  have hiR:Integrable (fun y=>8*q y*(1-W.core y)*toL2 g.leviCivitaData univ R.val y*η y) g.volumeMeasure:=by
    convert (hrm.const_mul 8).integrable_mul η.memLp using 1
    congr 1
    funext y
    simp only [Pi.mul_apply]
    ring
  calc
    _=(∫y,8*q y*toL2 g.leviCivitaData univ Q y*η y-
      8*q y*(1-W.core y)*toL2 g.leviCivitaData univ R.val y*η y ∂g.volumeMeasure):=by
      apply integral_congr_ae
      filter_upwards [hZ] with y hz
      linear_combination 8*q y*η y*hz
    _=_:=integral_sub hiQ hiR

 theorem nativeSupportedSignedEnergy_closed_form
    (Y:nativeSupportedSourcePairSpace b)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))) (η:H1Zero g.leviCivitaData univ):
    closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (nativeSupportedSignedEnergy W Y R) η=
      closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (W.Q Y.val) η+
      closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
        (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val) η-
      closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const R.val η:=by
  change closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
    (W.Q Y.val+energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val-R.val) η=_
  let B:=closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
  have hlin(q c r:H1Zero g.leviCivitaData univ):B (q+c-r) η=B q η+B c η-B r η:=by
    have hs:=congrArg (fun L:H1Zero g.leviCivitaData univ →L[ℝ] ℝ=>L η) (map_sub B (q+c) r)
    have ha:=congrArg (fun L:H1Zero g.leviCivitaData univ →L[ℝ] ℝ=>(L-B r) η) (map_add B q c)
    exact hs.trans ha
  exact hlin _ _ _

#print axioms nativeSupportedSignedEnergy_ae
#print axioms nativeSupportedSignedEnergy_full_reaction_integral
#print axioms nativeSupportedSignedEnergy_closed_form
end Yamabe3.Analysis.SpherePolar
