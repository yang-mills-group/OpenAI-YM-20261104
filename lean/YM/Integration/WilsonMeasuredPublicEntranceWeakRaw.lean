import YM.Integration.WilsonMovingForkReporterBothArms
import YM.Integration.WilsonPhysicalStationThermalPair

/-! On either original Scribe port the same named weak field is the fitted thermal
input on its genuine ladder, including every raw component of that input. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceWeakRaw
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open WilsonMovingForkReporterBothArms (Filed)
open Further.CorrectedLift (ladder)
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
set_option maxRecDepth 6500 in
theorem original {J₀:ℝ→tower S}{J:Scaling S}{V:∀i,Vane R.family i}{H:(Bel R.family.book).Hierarchy}
    {i d:ℕ}(inside:d ≤ i)(check:(V i).checked f H i){M B:ℝ}
    (paid:Filed (f:=f) (l:=l) J₀ J V d i M B)(z:(Bel R.family.book).Field d):
    let k:Fin (i+1):=⟨d,Nat.lt_succ_of_le inside⟩
    ∃ a:Arm R.family S (l:Filter _) d (J.U i d z),
      (∀p,a.source p=(V i).wheel.atCut p k z) ∧
      (∀p:ℕ×ℕ,∀top:(V i).k<p.1,
        a.source p=WilsonPhysicalStationThermalPair.raw R (V i) k (p:=p.2) check top (ladder R.family d z)) ∧
      ∀ᶠ p:ℕ×ℕ in f.fuse,Cards.PaidAt R.family.S p.1 p.2 (purchaseWidth (V i))
        (R.family.beta p.1 p.2) (B*‖(J₀ (V i).wheel.r d).symm (J.U i d z)‖)
        (R.family.O p.1 p.2 (a.source p) 0):=by
  let k:Fin (i+1):=⟨d,Nat.lt_succ_of_le inside⟩
  let w:=(J₀ (V i).wheel.r d).symm (J.U i d z)
  have line:=paid w
  dsimp only at line
  rw [show J₀ (V i).wheel.r d w=J.U i d z from (J₀ _ _).apply_symm_apply _,
    (J.U i d).symm_apply_apply] at line
  obtain ⟨_,a,raw,fee⟩:=line
  have cash(p):a.source p=(V i).wheel.atCut p k z:=by simpa only [heightV,dif_pos inside] using raw p
  refine ⟨a,cash,fun p top=>?_,fee⟩
  exact (cash p).trans (WilsonPhysicalStationThermalPair.lifted R (V i) k (p:=p.2) check top z).symm
end YM.Integration.WilsonMeasuredPublicEntranceWeakRaw
