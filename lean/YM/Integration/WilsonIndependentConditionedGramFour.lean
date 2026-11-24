import YM.Integration.WilsonIndependentConditionedBankFour
import YM.Integration.WilsonIndependentConditionedGramCampus

/-! The signed four-corner estimate on the original elected marked course, before any cutoff, tests or locations. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramFour
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedPairFiledSemester (Tested)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D e k u u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC

open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedBankFour (Enrolled)

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h (2*k) u e)(l d:J→ℕ)(admit:∀i,l i<d i)
    (own:∀s,Rails (l s) k u₀ e)(b:ℕ)(reserve:u+b ≤ u₀)(depth:2*k ≤ b)
    (I:Initialize G)(ι:J→Type*)(survey:(s:J)→ι s→Bool):
    let Q:=deck (G:=G) l d admit
    let S:SectionData ((primes G).F h):=(primes G).T h
    ∃(L M:Credit)(rate:J→J→Credit)(coins:Prices)(A:(s:J)→ι s→Alma (R.family.labels.level (l s))→ℝ),
      (∀s i t,0 ≤ A s i t) ∧ ∀ᶠ j:ℕ in atTop,
        ∃(W:ChorusLine (hol G) S p e C C C)(Y:Torch (hol G) S p rails C C C)
          (port:(s:J)→Home R (Q s) (own s) j),
          W.arch=Y.L ∧ Y.L.V.draws=R.family.path.levels ∧ Y.L.V.paid=R.metals.O ∧
          Y.L.V.y=zz R.family.path.levels ∧ Y.L.V.anchor=j ∧
          FramesR (hol G) Y.L.V C C Q C ∧ HorizonP (hol G) Y.L.V C C Q ∧
          (∀s t,WilsonIndependentConditionedGramCampus.Paid Y.L.V (Q s) (Q t) k (rate s t)) ∧
          ∀(host m K N:ℕ),j ≤ host → host ≤ m → m ≤ K → K ≤ N →
          ∀c:(s:J)→ι s→Verse (R.family.labels.level (l s)),
            ∃T:Assigned R Q own Y.L.V coins j port ι
              (fun s i=>Shrine (plate (sectionAt R I (survey s i) (l s)) (admit s)) (c s i))
              (fun s i=>charge e (c s i) (A s i)) u b host m K N, Enrolled T L M :=by
  classical
  intro Q S
  obtain ⟨L,M,estimate⟩:=WilsonIndependentConditionedBankFour.appointed Q own
  obtain ⟨rate,coins,A,nn,opening⟩:=WilsonIndependentConditionedGramCampus.original R simple v funded
    p rails l d admit own b reserve depth I ι survey
  refine ⟨L,M,rate,coins,A,nn,?_⟩
  filter_upwards [opening] with j event
  obtain ⟨W,Y,port,track,levels,clock,axis,anchor,frames,horizon,paid,receipts⟩:=event
  refine ⟨W,Y,port,track,levels,clock,axis,anchor,frames,horizon,paid,?_⟩
  intro host m K N begun older cut top c
  obtain ⟨T⟩:=receipts host m K N begun older cut top c
  exact ⟨T,estimate T older⟩

end YM.Integration.WilsonIndependentConditionedGramFour
