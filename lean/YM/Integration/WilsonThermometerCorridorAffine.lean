import YM.Integration.WilsonThermometerWeakMixedBoard
import YM.Integration.WilsonThermometerCorridorWalk
import YM.Integration.WilsonThermometerMixedAmplitude

/- Keep the already deposited, jointly named complete Wilson numerator at f.
   Its two tagged pronunciations are put on the very same original hard gallery,
   at the smaller radius paid by the three genuine lower physical rides. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorAffine
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput WilsonThermometerOwnOffsetNectar
open scoped Topology BigOperators Classical
set_option quotPrecheck false
open WilsonThermometerMixedAmplitude
variable {G:Gauge}{n:Side}
local notation "J"=>Stock.census (Fin 3)

private theorem sloped {q:ℂ}(neq:q≠0)(a:Poly (J))(depth:∀s:(J).Mode,a.part s≠0 → 2 ≤ s.val.card):
    Line q 0 a (q⁻¹ • a):=by
  constructor
  · intro s small
    have zero:a.part s=0:=by by_contra alive;have many:=depth s alive;omega
    rw [sub_zero,Poly.part_smul,zero,mul_zero]
  · rw [sub_zero,zero_add,smul_smul,mul_inv_cancel₀ neq,one_smul]

private theorem flags {q:ℂ}(A B C:Box n→Poly (J))(s:Support n)(rows:∀i,Line q (A i) (B i) (C i)):
    Line q (Accent.field A s) (Accent.field B s) (Accent.field C s):=by
  unfold Accent.field
  apply WilsonThermometerMixedAmplitude.finite
  intro p _
  unfold Accent.grid
  split
  · exact WilsonThermometerMixedAmplitude.products _ _ _ _ (fun i _=>rows i)
  · exact WilsonThermometerMixedAmplitude.same _

theorem original (P:Rep G n) (Φ:Fin 3 → Config G n→ℂ)
    (κ:Fin 3→Box n→ Config G n→ℂ) {o:Fin 3→Site n} {δ:ℝ}(dp:0<δ)
    (H:Support n→ Config G n→Poly (J))(K:Box n→ Config G n→Poly (J))
    (chart:Carton o H K P.p.threshold) (U:Config G n):
    let Z:=WilsonMixedTaggedStart.lifted (R:=P) Φ κ δ H K U
    Line (δ:ℂ) (specialize (J) 0 Z) (specialize (J) (δ:ℂ) Z) (specialize (J) 1 Z):=by
  dsimp only
  have neq:(δ:ℂ)≠0:=Complex.ofReal_ne_zero.mpr dp.ne'
  rw [WilsonMixedTaggedStart.projected Φ κ 0 chart U,WilsonMixedTaggedStart.projected Φ κ (δ:ℂ) chart U,
      WilsonMixedTaggedStart.projected Φ κ 1 chart U]
  simp only [zero_mul,zero_smul,mul_inv_cancel₀ neq,one_smul,one_mul]
  unfold restore
  apply WilsonThermometerMixedAmplitude.scaled
  apply WilsonThermometerMixedAmplitude.product
  · apply WilsonThermometerMixedAmplitude.passed
    apply WilsonThermometerMixedAmplitude.add (WilsonThermometerMixedAmplitude.same _)
    apply WilsonThermometerMixedAmplitude.finite
    intro i _
    exact sloped neq _ ((chart.exp i).2 U)
  · apply flags
    intro i
    exact WilsonThermometerMixedAmplitude.add (WilsonThermometerMixedAmplitude.same _) (sloped neq _ ((chart.flag i).2 U))
end YM.Integration.WilsonThermometerCorridorAffine
end
