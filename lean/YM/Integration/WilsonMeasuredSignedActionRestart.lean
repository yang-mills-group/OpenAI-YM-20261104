import YM.Integration.WilsonIndependentRegisteredUnaryFactory
import YM.Integration.WilsonPositionProgramBlockedTrialCone

/-! The signed transfer on the enrolled original history accepts a new
one-source voice at any actual date. The older conditional vacuum, the
full emitted density and the incoming forced terms stay on the same post. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4608
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionRestart
open Filter Finset Function Lattice RG Wilson Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations
open scoped Classical Topology
section localStep
variable {G:Gauge}{d N per t:ℕ}{F:Frame G d}{H:History G}{B:SectionData F}{P:Hol G}{W:Worth}
variable {D:GaugeDoor (H.rep N per (t+1)) (H.rep N per t)}{up:Desk G (H.S.side (t+1) per)}
variable {price η v:ℝ}{keys:Set Wing}{U:Heading F}
private theorem reading (tool:Tool F H N per t)(cap:Tool.Cap tool B P W D U price η v keys)
    (well:Well (H.rep N per (t+1)) up (Real.sqrt (H.levels.clock.forcedAllowance (t+1))))
    (room:roomCost H.levels W)(bank:Bank W H.levels)
    (V:Voice F H per (t+1))(hv:Heard B H N per P (t+1) V)(copied:Chorus H N per (t+1) V):
    ∃Z:Voice F H per t,Heard B H N per P t Z ∧ Responds B H N per W t V Z ∧ Chorus H N per t Z ∧
      ∀v,F.coeffSize (Z.index v-U.leads (H.S.block t) (V.index v)) ≤
        barunit (H.S.block t)*F.coeffSize (F.core (V.index v)):=by
  obtain ⟨Z,earn,replies,_,closes,registered⟩:=Matric.sends room bank tool cap well hv copied
  refine ⟨Z,earn,replies,closes,?_⟩
  intro x
  let graph:=Matric.measure hv tool.up well
  have same : Z.plays x=graph.point tool (V.index x):=registered hv x
  rw [← earn.currents x,same]
  exact graph.signedPoint tool cap well (V.index x)
end localStep

variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T){d N per t:ℕ}
local notation "F" => R.family.labels.level d
local notation "H" => R.family.path
local notation "B" => R.family.localSection d
local notation "P" => R.family.params

include L in
theorem edge (simple:G.Simple)(early:R.t d≤t)(live:t<N)
    (V:Voice F H per (t+1))(hv:Heard B H N per P (t+1) V)(copied:Chorus H N per (t+1) V):
    ∃ (U:Heading F)(Z:Voice F H per t),
      WilsonIndependentUnaryPrincipal.Signed U ((H).levels.budget (t+1)).threshold ((H).levels.budget t).threshold ∧
      Heard B H N per P t Z ∧ Responds B H N per R.w t V Z ∧ Chorus H N per t Z ∧
      ∀v, (F).coeffSize (Z.index v - U.leads ((H).S.block t) (V.index v)) ≤
        barunit ((H).S.block t)*(F).coeffSize ((F).core (V.index v)):=by
  let branch:=L.yields N per
  let session:=branch.steps t (Nat.zero_le _) live
  have floor: d+3≤R.alloy.B.a.clock.J t:=(R.accepts d).trans (R.alloy.B.a.fits.mono early)
  let tool:=session.castT R.b branch.choice floor
  obtain ⟨U,keys,head,book⟩:=Boutique.signedStoredTickets simple R.b session branch.choice floor R.tuning.receipts
  have well:=branch.notices (fun i=>Boutique.brochure R.T i per R.tuning.receipts) (Nat.zero_le (t+1)) live
  refine ⟨U,?_⟩
  obtain ⟨Z,ear,returned,quiet,numeric⟩:=reading tool book well R.b.clock.room R.b.clock.bank V hv copied
  exact ⟨Z,head,ear,returned,quiet,numeric⟩

end YM.Integration.WilsonMeasuredSignedActionRestart
end
