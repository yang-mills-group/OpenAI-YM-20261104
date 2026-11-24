import YM.Integration.WilsonOriginalPublicTrialPhaseRace
import YM.Integration.WilsonOriginalPublicTrialPhaseFlat

/-! All original scalar and occupied readings on one finite height-zero trajectory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseTrajectory
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local Next.Foundations
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm RG05Readout RG05Readout.Address
open WilsonOriginalPublicTrialPhaseAccumulated WilsonOriginalPublicTrialPhaseRace
open scoped Classical BigOperators ContDiff
variable {G:Gauge}(R:Run G){N per:ℕ}
local notation "C" => R.family
local notation "A" => R.alloy.B.a
local notation "H" => (C).path
local notation "P" => (H).rep N per
local notation "O" => (H).levels.clock.op
local notation "F" => (C).labels.level 0
local notation "loc" => (C).localSection 0

set_option maxHeartbeats 1300000 in
theorem original (hG:G.Simple)(purchase:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:RG05Readout.Many.Storage (C) R.doors)(u h:ℕ)(live:u+h≤N)
    (o:∀i,Site ((C).side (u+i) per))(parent:∀i, i<h →
      ((O) (u+i) per).ratio.parent (o (i+1))=o i)
    (grade:∀i,i<h→3≤(A).clock.J (u+i))
    (hit:∀i,i<h→Push.Local.hitWidth ((P) (u+i)).p*Push.Local.kappa (H) (u+i)≤1)
    (fine:∀i,i<h→Push.Local.kappa (H) (u+(i+1))≤1)
    (r:ℝ)(top:Coefficient (F) ((C).side (u+h) per))
    (fmt:top.Format (o h) (C).params ((P) (u+h)))
    (rem:top.remBound (o h) ((P) (u+h)) (Push.Local.kappa (H) (u+h)) r):
    let w:=fun i=> wage (C).S r (u+h) (u+i)
    ∃bank:∀(i:ℕ),i≤h → Coefficient (F) ((C).side (u+i) per),
      bank h le_rfl=top ∧
      (∀i (e:i≤h),(bank i e).Format (o i) (C).params ((P) (u+i)) ∧
        (bank i e).remBound (o i) ((P) (u+i)) (Push.Local.kappa (H) (u+i)) (w i)) ∧
      ∀i (e:i<h),‖(bank i e.le).x 0‖≤w i ∧ ∀z:ℂ,
        Ride ((O) (u+i) per) (o (i+1)) (o i) (R.doors N per (u+i) (by omega)) 1
          (row (bank (i+1) e) (o (i+1)) (loc) ((P) (u+(i+1))) z)
          (row (bank i e.le) (o i) (loc) ((P) (u+i)) (z+(bank i e.le).x 0))
          ((2+Doors.rate ((C).S.block (u+i)))*w (i+1)+‖z‖):=by
  intro w
  let Seat:=fun i=> {q:Coefficient (F) ((C).side (u+i) per)//
    q.Format (o i) (C).params ((P) (u+i)) ∧ q.remBound (o i) ((P) (u+i)) (Push.Local.kappa (H) (u+i)) (w i)}
  let head:Seat h:=⟨top,fmt,by simpa only [w,terminal] using rem⟩
  have edge (i)(e:i<h)(x:Seat (i+1)):
      ∃y:Seat i, ‖y.val.x 0‖≤w i ∧ ∀z:ℂ,
        Ride ((O) (u+i) per) (o (i+1)) (o i) (R.doors N per (u+i) (by omega)) 1
          (row x.val (o (i+1)) (loc) ((P) (u+(i+1))) z)
          (row y.val (o i) (loc) ((P) (u+i)) (z+y.val.x 0))
          ((2+Doors.rate ((C).S.block (u+i)))*w (i+1)+‖z‖):=by
    have hR:w i=Doors.rate ((C).S.block (u+i))*w (i+1):=step (C).S r (u+h) (u+i)
    obtain ⟨k,f,c,a,pass⟩:= WilsonOriginalPublicTrialPhaseAccumulated.original R hG purchase stock
      (m:=u+i) (N:=N) (per:=per) (by omega) (grade i e) (o (i+1)) x.val (hit i e) (fine i e) _
      x.property.1 x.property.2
    rw [parent i e] at f c pass
    refine ⟨⟨k,f,by rw [hR];exact c⟩,?_,pass⟩
    change ‖k.x 0‖≤w i
    rw [hR]
    exact a
  let next:=fun i (e:i<h) (x:Seat (i+1))=>(edge i e x).choose
  let bank:=back h head next
  refine ⟨fun i e=>(bank i e).val,?_,fun i e=>(bank i e).property,?_⟩
  · exact congrArg Subtype.val (back_head h head next)
  · intro i e
    have p:bank i e.le=next i e (bank (i+1) e):=back_step h head next i e
    simpa only [p] using (edge i e (bank (i+1) e)).choose_spec

end YM.Integration.WilsonOriginalPublicTrialPhaseTrajectory
end
