import YM.Integration.WilsonIndependentRegisteredUnaryTickets
import YM.Integration.WilsonIndependentRegisteredUnaryGraph
import YM.FullVolume.Gables.Vendee

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentRegisteredUnaryFactory
open Filter Finset Lattice RG Wilson Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations
open scoped Classical Topology

variable {G:Gauge} (R:Run G) {T:Campaign R} (L:Pillars R T) {d N p m:ℕ}
local notation "Fr" => R.family.labels.level d
local notation "tally" => (R.family.labels.level d).coeffSize
local notation "block" => R.family.S.block m

include L in
/-- The named incoming and outgoing coefficients are the two actual stored
factory columns in one registered history. The same signed heading works for
every source vector at the stated cutoff and period. -/
theorem original (hg:G.Simple) (early:R.t d ≤ m)(live:m<N) :
    ∃ U:Heading Fr,
      WilsonIndependentUnaryPrincipal.Signed U (R.alloy.B.a.budget (m+1)).threshold (R.alloy.B.a.budget m).threshold ∧
      ∀ v:R.family.label d,
        let a:=(R.family.factory d N p).entries (m+1) v
        let b:=(R.family.factory d N p).entries m v
        tally (b.x-U.leads block a.x) ≤ barunit block*tally ((Fr).core a.x) := by
  let branch:=L.yields N p
  let session:=branch.steps m (Nat.zero_le _) live
  have floor:= (R.accepts d).trans (R.alloy.B.a.fits.mono early)
  let tool:=session.castT R.b branch.choice floor
  obtain ⟨U,keys,hU,book⟩:=Boutique.signedStoredTickets hg R.b session branch.choice floor R.tuning.receipts
  obtain ⟨M,_,registered,entitled,newer⟩:=L.ports d N p (early.trans live.le)
  have old:=entitled.earned (m+1) (early.trans (Nat.le_succ _)) live
  have well:=branch.notices (fun i=>Boutique.brochure R.T i p R.tuning.receipts) (Nat.zero_le (m+1)) live
  let graph:=Matric.measure old tool.up well
  refine ⟨U,hU,?_⟩
  intro v a b
  have first : a = (M.tone (m+1)).plays v := congr_fun (congr_fun registered _) _
  have last : b = (M.tone m).plays v := congr_fun (congr_fun registered _) _
  have same : a.x = (M.tone (m+1)).index v := (congrArg Coefficient.x first).trans (old.currents v)
  have stored : b = graph.point tool a.x := by
    rw [last,same]
    exact (newer m early live).2.2 old v
  rw [stored]
  exact graph.signedPoint tool book well a.x

end YM.Integration.WilsonIndependentRegisteredUnaryFactory

