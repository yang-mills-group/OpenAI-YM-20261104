import YM.Integration.WilsonOriginalPublicTrialPhaseGroup
import YM.Integration.WilsonOriginalPublicTrialPhaseZero
import YM.Contacts.Leap.String
import YM.Contact.Nested

/-! One expanding-radius step for whole tiles on the actual old Wilson vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseRenew
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(R:Run G){j N m per:ℕ}
local notation "C" => R.family
local notation "H" => (C).path
local notation "P" => (H).rep N per (m+1)
local notation "Q" => (H).rep N per m
local notation "A" => (H).levels
local notation "O" => (A).clock.op m per
local notation "δ" => Bandage.renal (A) m
local notation "cap" => apron (A) m

private theorem once {n:Side}{V:Type}[Fintype V](o:V→Site n)(inc:Injective o):Occupancy o 1:=by
  classical
  intro y
  apply card_le_one.mpr
  intro a ha b hb
  exact inc ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)

theorem original (cater:Cater (C) R.doors)(live:m<N)(jm : j ≤ m)
    (gap:ℕ)(z:Site ((C).side (m+1) per))(big:8≤gap)
    (room:pdist ((O).ratio.parent z)+pdist ((O).ratio.parent z)+((A).budget m).B*gap<
      ((C).S.toDepth jm per).count.val):
    let T:=tilesAt (C).S per (jm.trans m.le_succ)
    let U:=tilesAt (C).S per jm
    let o:=fun i:Unit×T.Cell=>T.copyMap i.2 z
    let b:=fun i:Unit×T.Cell=>U.copyMap i.2 ((O).ratio.parent z)
    ∀ (w w' bill:Unit×T.Cell→ℝ)(X:Unit×T.Cell→Three G ((C).side (m+1) per))
      (Y:Unit×T.Cell→Three G ((C).side m per))
      (F:Config G ((C).side (m+1) per)→Poly (Stock.census (Unit×T.Cell)))(e:ℝ),
      MenuBoard (P) X F o w e 1→ ((P).p.supportExponent)-4≤e →
      (∀i,0<w i)→(∀i,0<w' i)→(∀i,2*w i*bill i≤1)→(∀i,w' i≤(δ*w i)*mintK gap)→
      (∀i,Ride (O) (o i) (b i) (R.doors N per m live) 1 (X i) (Y i) (bill i))→
      MenuBoard (Q) Y ((O).push (P).beta F) b w' ((A).budget m).supportExponent 1:=by
  intro T U o b w w' bill X Y F e start pitch pos pos' audit lease rides
  have parents:(O).ratio.parent ∘ o=b:=funext fun i=>WilsonOriginalPublicTrialPhaseTileSites.parent R jm i.2 z
  have sep(a a':Unit×T.Cell)(ne:a≠a'):((A).budget m).B*gap ≤ separation (b a) (b a'):=by
    apply Nat.le_of_lt
    exact Contacts.Nested.nested_separation jm (fun _:Unit=>(O).ratio.parent z) _ (fun _ _=>room)
      (fun a b h=>(h (Subsingleton.elim a b)).elim) (a.2,()) (a'.2,())
      (fun h=>ne (Prod.ext (Subsingleton.elim ..) (congrArg Prod.fst h)))
  have inj:Injective b:=by
    intro a a' eq
    by_contra ne
    have hsep:=sep a a' ne
    rw [eq,separation_self] at hsep
    have hB:=((A).budget m).B_pos
    exact (show 0<((A).budget m).B*gap from Nat.mul_pos hB (by omega)).not_ge hsep
  have ino:Injective o:=fun a a' h=>inj ((congrFun parents a).symm.trans ((congrArg (O).ratio.parent h).trans (congrFun parents a')))
  have ar:1≤cap:=Nat.mul_pos (Nat.succ_pos _) (pow_pos ((C).S.block m).property _)
  have hO:Occupancy o cap:=fun a=>(once o ino a).trans ar
  have hO':Occupancy ((O).ratio.parent ∘ o) cap:=by rw [parents];exact fun a=>(once b inj a).trans ar
  obtain ⟨a,t,course,-,-⟩:=cater.tiers m N per live
  have hp:(P).p=(A).budget (m+1):=(R.makes.wilson.represents N per (m+1) live).vac
  rw [hp] at pitch
  have rep:Repegs b ((A).budget m).B (fun i=>δ*w i) w' (1/2) 1 (Stock.census (Unit×T.Cell)) :=
    Leap.palms lease pos' (fun i=>mul_pos course.poses.hats.1 (pos i)) big ((A).budget m).B_pos sep
  rw [←parents] at rep rides
  have issue:=course.send R.makes.wilson live start pitch (ν:=fun _=>1) (by simp) pos rides hO hO' audit pos' rep
  simpa only [parents,inv_one,one_smul] using issue

end YM.Integration.WilsonOriginalPublicTrialPhaseRenew
