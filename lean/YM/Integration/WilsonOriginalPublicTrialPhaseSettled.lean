import YM.Integration.WilsonOriginalPublicTrialPhaseTrajectory
import YM.Integration.WilsonOriginalPublicTrialPhaseArrears

/-! The actual settled phase and all original occupied rows on a single captured trajectory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseSettled
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local Next.Foundations MergeProof MergeProof.Accent
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm RG05Readout RG05Readout.Address
open WilsonOriginalPublicTrialPhaseAccumulated WilsonOriginalPublicTrialPhaseRace
open WilsonOriginalPublicTrialPhaseArrears
open scoped Classical BigOperators ContDiff
variable {G:Gauge}(R:Run G){N per:ℕ}
local notation "C" => R.family
local notation "A" => R.alloy.B.a
local notation "H" => (C).path
local notation "P" => (H).rep N per
local notation "O" => (H).levels.clock.op
local notation "F" => (C).labels.level 0
local notation "loc" => (C).localSection 0

set_option maxHeartbeats 1600000 in
theorem original (hG:G.Simple)(purchase:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:RG05Readout.Many.Storage (C) R.doors)(u h:ℕ)(live:u+h≤N)
    (o:∀i,Site ((C).side (u+i) per))(parent:∀i, i<h →
      ((O) (u+i) per).ratio.parent (o (i+1))=o i)
    (grade:∀i,i<h→3≤(A).clock.J (u+i))
    (hit:∀i,i<h→Push.Local.hitWidth ((P) (u+i)).p*Push.Local.kappa (H) (u+i)≤1)
    (fine:∀i,i<h→Push.Local.kappa (H) (u+(i+1))≤1)
    (r:ℝ)(hr:0≤r)(top:Coefficient (F) ((C).side (u+h) per))
    (fmt:top.Format (o h) (C).params ((P) (u+h)))
    (rem:top.remBound (o h) ((P) (u+h)) (Push.Local.kappa (H) (u+h)) r):
    let w:=fun i=> wage (C).S r (u+h) (u+i)
    let raw:=(invoice top (o h) (loc) ((P) (u+h))).1
    let a:=gust (H) N per (u+h) raw u (Nat.le_add_right ..) 1 / (((P) u).eval 1:ℂ)
    ∃(bank:∀(i:ℕ),i≤h → Coefficient (F) ((C).side (u+i) per)) (z:ℕ→ℂ),
      bank h le_rfl=top ∧ z 0=0 ∧ z h=top.x 0-a ∧
      (∀i (e:i≤h),(bank i e).Format (o i) (C).params ((P) (u+i)) ∧
        (bank i e).remBound (o i) ((P) (u+i)) (Push.Local.kappa (H) (u+i)) (w i) ∧
        ‖z i‖≤WilsonOriginalPublicTrialPhaseArrears.factor*w i) ∧
      ∀i (e:i<h), Ride ((O) (u+i) per) (o (i+1)) (o i) (R.doors N per (u+i) (by omega)) 1
        (row (bank (i+1) e) (o (i+1)) (loc) ((P) (u+(i+1))) (z (i+1)))
        (row (bank i e.le) (o i) (loc) ((P) (u+i)) (z i))
        ((2+Doors.rate ((C).S.block (u+i)))*w (i+1)+‖z (i+1)‖):=by
  intro w raw a
  obtain ⟨bank,head,accounts,edges⟩:=WilsonOriginalPublicTrialPhaseTrajectory.original R hG purchase stock
    u h live o parent grade hit fine r top fmt rem
  let v:=fun i=>if e:i<h then (bank i e.le).x 0 else 0
  let z:=incurred v
  have price (i)(e:i<h):‖v i‖≤w i:=by simpa only [v,dif_pos e] using (edges i e).1
  have budget:=WilsonOriginalPublicTrialPhaseArrears.original (C).S u h r hr v price
  have inc (i)(e:i<h):z (i+1)+(bank i e.le).x 0=z i:=by simpa only [v,dif_pos e] using next v i
  let off:=top.x 0-z h
  have measure (i)(e:i≤h):
      (row (bank i e) (o i) (loc) ((P) (u+i)) (z i+off)).1
        =gust (H) N per (u+h) raw (u+i) (by omega):=by
    induction e using Nat.decreasingInduction with
    | self=>
      rw [head,gust_base]
      have hz:z h+off=top.x 0:=by unfold off; abel
      rw [hz,start]
    | of_succ i e ih=>
      have he:=((edges i e).2 (z (i+1)+off)).exactStep
      have hz:z (i+1)+off+(bank i e.le).x 0=z i+off:=by rw [add_right_comm,inc i e]
      rw [hz,one_smul,ih] at he
      rw [gust_step (H) N per (u+h) raw (show u+i<u+h by omega)]
      exact he
  have ground:=congrFun (measure 0 (Nat.zero_le _)) 1
  rw [WilsonOriginalPublicTrialPhaseFlat.settled _ _ _ _ (accounts 0 _).1] at ground
  simp only [Nat.add_zero] at ground
  have nz:(((P) u).eval 1:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (ne_of_gt
    (Extra.Histories.Tour.bright (H) R.makes.wilson N per u (by omega) 1))
  have exactA:a=off:=by
    change _/_=_
    rw [←ground]
    change (((P) u).eval 1:ℂ)*(0+off)/_=off
    rw [zero_add]
    field_simp
  refine ⟨bank,z,head,rfl,?_,fun i e=>⟨(accounts i e).1,(accounts i e).2,budget i e⟩,?_⟩
  · rw [exactA];unfold off;abel
  · intro i e
    simpa only [inc i e] using (edges i e).2 (z (i+1))

end YM.Integration.WilsonOriginalPublicTrialPhaseSettled
end
