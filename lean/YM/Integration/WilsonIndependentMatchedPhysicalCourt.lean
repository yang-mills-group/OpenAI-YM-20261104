import YM.Integration.WilsonMarkedIndependentNormalizedElection
import YM.Integration.WilsonIndependentMatchedInheritedStop
import YM.Integration.WilsonIndependentMatchedRosterPlanted
/-! The actual physical calendar funds all needed connector and older height rows before a field is fitted. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonIndependentMatchedPhysicalCourt
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped Topology BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}(R:Run G)

local notation "C" => Credit.leanC

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (out u e b:ℕ)(rails:Rails 0 out u e)(fit:out ≤ b):
    ∀ᶠ j:ℕ in atTop,∃V:Realm G (e+1) C,
      V.draws=R.family.path.levels ∧ V.paid=R.metals.O ∧ V.y=zz R.family.path.levels ∧ V.anchor=j ∧
      (∀s ≤ out,Dormitory V s u C) ∧ SpringD V out u b C:=by
  obtain ⟨chartEq,floor,_,fees,_⟩:=funded
  have awards:=reported (hol G) (primes G) floor fees
  filter_upwards [Mer.Patrol.continuity simple (chart_ok G) R.alloy.B.valid awards tendsto_id
    (by decide:0<1) rails b] with j seats
  obtain ⟨W,_,levels,ratio,calendar,start,_,_,paid⟩:=seats
  refine ⟨W.arch.V,levels,ratio.trans chartEq.symm,calendar,start,fun s hs=>(paid s hs 0 (Nat.zero_le _)).1,?_⟩
  simpa only [Nat.add_sub_of_le fit] using (paid out le_rfl (b-out) (Nat.sub_le ..)).2

open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterPlanted
open private flatEscort from YM.Integration.WilsonOriginalPublicPlantedOlderJoin

theorem older (G:Gauge)(k e u:ℕ)(E W:Credit):
    ∃cash:Credit,∀(V:Realm G (e+1) E),Dormitory V k u W →
      ∀(host m N:ℕ),V.anchor ≤ host → host ≤ m → m ≤ N → ∀(P:Era G ℝ)(wage:ℝ),Auth k P → Flush e u 1 P wage →
        response e u (cruises V.draws V.paid N k m host P) (cash.buy (Compar V.draws.S V.y host m)*wage):=by
  obtain ⟨cash,paid⟩:=bulkCert G k e u E W
  refine ⟨cash,?_⟩
  intro V grant host m N awake active fine P wage auth flush
  have escort:=flatEscort V awake active
  have room:=PadRank.frugal V awake active
  have pos:0 ≤ cash.buy (Compar V.draws.S V.y host m):=zero_le_one.trans (cash.purchase (room.pos escort))
  have earned:Flush e u 1 (cruises V.draws V.paid N k m host P) (cash.buy (Compar V.draws.S V.y host m)*wage):=by
    refine ⟨mul_nonneg pos flush.1,?_⟩
    intro j hj r _
    exact paid j hj r V grant host m (fun _=>1) N _ escort room fine P wage auth flush.1 flush.2
  exact ⟨earned,fun j hj=>WilsonIndependentMatchedCoverJoined.unit earned j hj⟩
end YM.Integration.WilsonIndependentMatchedPhysicalCourt
