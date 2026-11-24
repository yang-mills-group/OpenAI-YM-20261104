import YM.Integration.WilsonIndependentConditionedGramPrices
import YM.Integration.WilsonIndependentConditionedPairFour

/-! The public G table and its genuine four original/position assignments
use one selected marked course. The large angular moment needed by its
torch is retained in the actual receiving grant. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramCampus
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
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonIndependentConditionedGramPrices (profile)

def Paid (R:Realm G (e+1) C)(Q₁ Q₂:SealR G)(k:ℕ)(rate:Credit):Prop:=
  ∀(host m K N:ℕ),R.anchor ≤ host → host ≤ m → m ≤ K → K ≤ N →
    ∀(φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(B B' y:ℝ)(o:CellR),Amplitude φ B → Amplitude ψ B' →
    ∀(i:Alma Q₁.F)(j:Alma Q₂.F)(ω:Fin 0→YForest G),
      let x:=paceT R.draws.S m K
      let A:=rate.buy (epoch R host K)*(x^(Q₁.h+Q₂.h))⁻¹*
        (coinMat (Q₁.h+Q₂.h) e*profile φ y B*profile ψ y B')
      let bank:=embed (WilsonIndependentConditionedBankTable.measure R Q₁ Q₂ k m K N host φ ψ y o 0 ω i j)
      (∀q ≤ e,‖coeff q bank‖ ≤ A) ∧ ∀q ≤ e,belt q bank ≤ ((q+1:ℕ):ℝ)*A

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h (2*k) u e)(l d:J→ℕ)(admit:∀i,l i<d i)
    (own:∀s,Rails (l s) k u₀ e)(b:ℕ)(reserve:u+b ≤ u₀)(depth:2*k ≤ b)
    (I:Initialize G)(ι:J→Type*)(survey:(s:J)→ι s→Bool):
    let Q:=deck (G:=G) l d admit
    let S:SectionData ((primes G).F h):=(primes G).T h
    ∃(rates:J→J→Credit)(coins:Prices)(A:(s:J)→ι s→Alma (R.family.labels.level (l s))→ℝ),
      (∀s i t,0 ≤ A s i t) ∧ ∀ᶠ j:ℕ in atTop,
        ∃(W:ChorusLine (hol G) S p e C C C)(Y:Torch (hol G) S p rails C C C)
          (port:(s:J)→Home R (Q s) (own s) j),
          W.arch=Y.L ∧ Y.L.V.draws=R.family.path.levels ∧ Y.L.V.paid=R.metals.O ∧
          Y.L.V.y=zz R.family.path.levels ∧ Y.L.V.anchor=j ∧
          FramesR (hol G) Y.L.V C C Q C ∧ HorizonP (hol G) Y.L.V C C Q ∧
          (∀s t,Paid Y.L.V (Q s) (Q t) k (rates s t)) ∧
          ∀(host m K N:ℕ),j ≤ host → host ≤ m → m ≤ K → K ≤ N →
          ∀c:(s:J)→ι s→Verse (R.family.labels.level (l s)),
            Nonempty (Assigned R Q own Y.L.V coins j port ι
              (fun s i=>Shrine (plate (sectionAt R I (survey s i) (l s)) (admit s)) (c s i))
              (fun s i=>charge e (c s i) (A s i)) u b host m K N):=by
  classical
  intro Q S
  choose rates pay using fun (s t:J)=>WilsonIndependentConditionedGramPrices.original (hol G) (Q s) (Q t) k e u C C C C
  choose A nn salary using fun (s:J)(i:ι s)=>WilsonIndependentConditionedPairProbeInput.named R I (survey s i)
    (l s) (d s) (admit s) (own s)
  obtain ⟨coins,semester⟩:=WilsonIndependentConditionedPairProbeSemester.original R simple v funded
    p rails l d admit own b reserve depth
  refine ⟨rates,coins,A,nn,?_⟩
  filter_upwards [semester,WilsonIndependentConditionedPairFour.preparation R simple v funded l d admit e] with j lane insurance
  obtain ⟨W,Y,level,reset,age,anchor,one,bills,frame,horizon,ports,received⟩:=lane
  let port:=fun s:J=>(ports s).some
  refine ⟨W,Y,port,one,level,reset,age,anchor,frame,horizon,?_,?_⟩
  · intro s t
    apply pay s t Y.L.V (horizon s).some (horizon t).some
    · simpa only [two_mul] using (bills (2*k) le_rfl 0 (Nat.zero_le _)).1
    · exact Nat.add_le_add (own s).hk (own t).hk
  intro host m K N live older cut vac c
  choose X torch choir files stamps home birth top compare upper field same amount using fun (s:J)(i:ι s)=>
    salary s i j m K N (port s) (live.trans older) cut vac (c s i)
  have draw (s:J)(i:ι s):(X s i).ax=Y.L.V.draws:=(files s i).trans level.symm
  have clock (s:J)(i:ι s):(X s i).tx=Y.L.V.paid:=(stamps s i).trans reset.symm
  refine ⟨⟨X,torch,choir,draw,clock,home,birth,top,compare,upper,field,same,amount,?_,?_⟩⟩
  · intro s i
    have reach:=insurance (port s).source.L.V (port s).levels (port s).reset (port s).age (port s).anchor s
    change AheadT (hol G) (X s i).L.L.V C C (Q s) C
    rw [torch]
    exact reach.some
  · intro pick ζ a base φ y t z o B gain room ht clearance sizes bounds
    exact WilsonIndependentConditionedPairProbeHearings.original Q own C C C C Y.L.V coins u b received
      (fun s=>X s (pick s)) host m K N (anchor.le.trans live) older cut vac
      (fun s=>draw s _) (fun s=>clock s _) (fun s=>home s _) (fun s=>birth s _) (fun s=>top s _)
      ζ a base φ y t z o B gain room ht clearance sizes bounds

end YM.Integration.WilsonIndependentConditionedGramCampus
