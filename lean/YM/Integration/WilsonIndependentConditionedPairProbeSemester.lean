import YM.Integration.WilsonIndependentConditionedBankEstate
import YM.Integration.WilsonIndependentConditionedPairProbes

/-! Original election for both heterogeneous input fields and their common three-mask receiver. The two source torches may have different horizons but read the same reset and unmarked history. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionedPairProbeSemester
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairProbes (Prices Heard)
open scoped Topology BigOperators Classical

variable {G:Gauge}{h D e k u u₀:ℕ}
local notation "C" => Credit.leanC

structure Home (R:Run G)(Q:SealR G)(own:Rails Q.h k u₀ e)(j:ℕ) where
  origin : ChorusLine (hol G) Q.ans Q.path e C C C
  source : Torch (hol G) Q.ans Q.path own C C C
  levels : source.L.V.draws=R.family.path.levels
  reset : source.L.V.paid=R.metals.O
  age : source.L.V.y=zz R.family.path.levels
  anchor : source.L.V.anchor=j
  one : origin.arch=source.L

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h (2*k) u e)(l d:Fin 2→ℕ)(admit:∀i,l i<d i)
    (own:∀i,Rails (l i) k u₀ e)(b:ℕ)(reserve:u+b≤u₀)(depth:2*k≤b):
    let Q:=deck (G:=G) l d admit
    let S:SectionData ((primes G).F h):=(primes G).T h
    ∃coins:Prices,∀ᶠ j:ℕ in atTop,
      ∃(W:ChorusLine (hol G) S p e C C C)(Y:Torch (hol G) S p rails C C C),
        Y.L.V.draws=R.family.path.levels ∧ Y.L.V.paid=R.metals.O ∧ Y.L.V.y=zz R.family.path.levels ∧
        Y.L.V.anchor=j ∧ W.arch=Y.L ∧
        (∀r≤2*k,∀lag≤b-2*k,Dormitory Y.L.V r u C ∧ SpringD Y.L.V r u (r+lag) C) ∧
        FramesR (hol G) Y.L.V C C Q C ∧ HorizonP (hol G) Y.L.V C C Q ∧
        (∀i,Nonempty (Home R (Q i) (own i) j)) ∧
        Heard (H:=hol G) Q own C C C C Y.L.V coins u b:=by
  classical
  intro Q S
  obtain ⟨coins,read⟩:=WilsonIndependentConditionedPairProbes.rooms (H:=hol G) Q own C C C C u b reserve
  have lanes:∀ᶠ j:ℕ in atTop,∀i,Nonempty (Home R (Q i) (own i) j):=by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [WilsonIndependentConditionedBankEstate.original R simple v funded (admit i) (own i) l d admit 0]
      with j issued
    obtain ⟨W,Y,lv,ch,age,anch,one,_⟩:=issued
    exact ⟨⟨W,Y,lv,ch,age,anch,one⟩⟩
  refine ⟨coins,?_⟩
  filter_upwards [WilsonIndependentConditionedBankEstate.original R simple v funded p rails l d admit (b-2*k),lanes]
    with j common inputs
  obtain ⟨W,Y,lv,ch,age,anch,one,bills,frame,horizon⟩:=common
  have span:2*k+(b-2*k)=b:=by omega
  have spring:SpringD Y.L.V (2*k) u b C:=span ▸ (bills (2*k) le_rfl (b-2*k) le_rfl).2
  exact ⟨W,Y,lv,ch,age,anch,one,bills,frame,horizon,inputs,
    read Y.L.V spring (fun r hr=>(bills r hr 0 (Nat.zero_le _)).1)⟩

end YM.Integration.WilsonIndependentConditionedPairProbeSemester
