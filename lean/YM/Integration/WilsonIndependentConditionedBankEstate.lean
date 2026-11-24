import YM.Integration.WilsonMarkedIndependentNormalizedElection

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonIndependentConditionedBankEstate
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

open WilsonMarkedIndependentNormalizedElection (deck)
local notation "C" => Credit.leanC

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(admit:∀i,l i<d i)(extra:ℕ):
    let Q:=deck (G:=G) l d admit
    let S:SectionData ((primes G).F h):=(primes G).T h
    ∀ᶠ j:ℕ in atTop, ∃(W:ChorusLine (hol G) S p e C C C)(Y:Torch (hol G) S p rails C C C),
      Y.L.V.draws=R.family.path.levels ∧ Y.L.V.paid=R.metals.O ∧ Y.L.V.y=zz R.family.path.levels ∧
      Y.L.V.anchor=j ∧ W.arch=Y.L ∧
      (∀k' ≤ k,∀lag ≤ extra,Dormitory Y.L.V k' u C ∧ SpringD Y.L.V k' u (k'+lag) C) ∧
      FramesR (hol G) Y.L.V C C Q C ∧ HorizonP (hol G) Y.L.V C C Q:=by
  intro Q S
  obtain ⟨chartEq,floor,_,fees,_⟩:=funded
  have awards:=reported (hol G) (primes G) floor fees
  filter_upwards [continuity simple (chart_ok G) R.alloy.B.valid awards tendsto_id p rails extra,
    ambassadors simple (chart_ok G) R.alloy.B.valid awards tendsto_id e Q (fun _=>rfl)] with j core access
  obtain ⟨W,Y,lv,ch,age,anch,_,agree,terms⟩:=core
  have framed:=access W.arch.V lv ch age anch
  refine ⟨W,Y,agree ▸ lv,agree ▸ ch.trans chartEq.symm,agree ▸ age,agree ▸ anch,agree.symm,?_,?_,?_⟩
  · exact agree ▸ terms
  · exact agree ▸ framed
  · exact agree ▸ fun i=>(framed i).map (fun q=>q.p)

end YM.Integration.WilsonIndependentConditionedBankEstate
end
