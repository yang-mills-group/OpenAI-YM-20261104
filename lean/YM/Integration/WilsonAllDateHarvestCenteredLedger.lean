import YM.Integration.WilsonAllDateHarvestStability
import YM.Integration.WilsonSeparatedOriginalCenteredBoard

/-! Earlier measured centering changes the scalar part of each singleton.
The witnesses, including their true forced arrays, are the very same paired
original regular and forced ledgers at every configuration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestCenteredLedger
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Records
open WilsonAllDateHarvestStability WilsonSeparatedOriginalCenteredBoard
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{I:Type}[Fintype I][DecidableEq I]{J:Census I}
variable {P:Rep G n} {rows:I→Three G n} {X:Config G n→Poly J} {o:I→Site n} {w:I→ℝ} {α:ℝ}

theorem shifted (bank:Ledger P rows X o w α) (v:I→ℂ):
    spice J v X=restore P (fun i U=>(rows i).2.1 U+v i)
      (fun i=>profile P.activities (rows i).2.2) bank.H bank.K := by
  funext U
  unfold spice
  rw [congr_fun bank.paid U]
  unfold restore
  let h:=Mach J (fun i=>(rows i).2.1 U)+∑i,bank.H i U
  let l:=Mach J v
  have adds:Mach J (fun i=>(rows i).2.1 U+v i)+∑i,bank.H i U=h+l:=by
    have eqn:Mach J (fun i=>(rows i).2.1 U+v i)=Mach J (fun i=>(rows i).2.1 U)+l:=by
      unfold l Mach
      simp only [send_add,sum_add_distrib]
    rw [eqn]
    unfold h
    abel
  have quiet:h.part J.quiet=0:=by
    unfold h
    simp only [Poly.part_plus,mute,Poly.part_sum,fun i=>hop J _ ((bank.legal.exp i).2 U),
      sum_const_zero,add_zero]
  rw [adds,pass_add quiet (show l.part J.quiet=0 from mute _ _),mul_comm (Poly.pass (Mach J v)),smul_mul_assoc]
  unfold h l
  rw [mul_right_comm]

section Physical
variable (C:Family G) {N j u per:ℕ}
local notation "Y" => C.path.rep N per

/-- Charge the centered, originally integrated cutoff product, with the
actual conditional means at the independent earlier receiving configuration. -/
theorem original (made:C.Makes) (f:I→Goods G (C.side N per)) (continuous:∀i,Continuous (f i))
    (jN:j ≤ N) (uj:u ≤ j) (U:Config G (C.side u per)) (rows:I→Three G (C.side j per))
    {o:I→Site (C.side j per)} {w:I→ℝ} {α:ℝ} {L:Config G (C.side j per)→Poly J}
    (base:Ledger (Y j) rows L o w α)
    (measured:Ledger (Y j) rows (gust C.path N per N (birth J (Y N) f) j jN) o w α):
    let v:=adjustment C f (uj.trans jN) U
    let dressed:=birth J (Y N) (fun i V=>v i+f i V)
    let singles:=fun i W=>(rows i).2.1 W+v i
    let hard:=fun i=>profile (Y j).activities (rows i).2.2
    Integrable dressed (prior G _) ∧
      gust C.path N per N dressed j jN=restore (Y j) singles hard measured.H measured.K ∧
      spice J v L=restore (Y j) singles hard base.H base.K := by
  intro v dressed singles hard
  have billed:Integrable (birth J (Y N) f) (prior G _):=
    (hatCont C N per f continuous (show Continuous ((Y N).eval) by
      rw [(made.wilson.starts ..).2];exact bare_cont _) J).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have trunc (x:Poly J):narrow (le_refl J.choices) x=x:=by
    ext z
    rw [narrow_right]
    rfl
  obtain ⟨integrated,chart⟩:=WilsonSeparatedOriginalCenteredBoard.reborn C f (le_refl J.choices) billed jN uj U
  simp only [trunc] at chart
  exact ⟨integrated,chart.trans (shifted measured v),shifted base v⟩

end Physical
end YM.Integration.WilsonAllDateHarvestCenteredLedger
