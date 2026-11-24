import YM.Integration.WilsonIndependentConditionedBankRulerPorts
import YM.Integration.WilsonIndependentConditionedBankSeats
import YM.Integration.WilsonIndependentConditionedBankRestored

/-! One pre-test school for all earlier observing rulers and both true original preparations. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankRulerSchool
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

open WilsonIndependentConditionedBankCorner (Bill input)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedPairProbes (Prices charge)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentFittedPivotCash (view)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentConditionedBankPublicGram (response)
open WilsonPositionProgramTrialHomeDose (publicDose)

open WilsonIndependentConditionedBankFour (Enrolled)
open WilsonIndependentConditionedBankMatrix (sample protocol)
open WilsonIndependentConditionedBankCash (amount reserve)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentConditionedBankPublicGram (residual)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonIndependentFittedMixedCash (embed)
open WilsonOlderFreshSoftCoverScalar (clock)

open WilsonIndependentConditionedBankFittedFees (age)
open WilsonIndependentConditionedBankShellPrice (wage)
open WilsonIndependentConditionedGramCampus (Paid)
open WilsonIndependentConditionedGramPrices (profile)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonSeparatedPrefixMovingCalendar (epoch)

open WilsonIndependentConditionedBankReport (salary panel debit)

open WilsonIndependentConditionedBankSeats (Resident raw submitted restored)
open WilsonIndependentConditionedBankRankedPorts (offered)
open WilsonIndependentConditionedBankRulerPorts (rehome)
open WilsonIndependentConditionedBankOpening (Earned)

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h (2*k) u e)(l d:J→ℕ)(admit:∀i,l i<d i)
    (own:∀s,Rails (l s) k u₀ e)(b:ℕ)(reserve:u+b ≤ u₀)(depth:2*k ≤ b)
    (I:Initialize G)(ι:J→Type*)(survey plain:(s:J)→ι s→Bool):
    let Q:=deck (G:=G) l d admit
    let S:SectionData ((primes G).F h):=(primes G).T h
    let types:=fun s=>ι s×Bool
    ∃(C₁ C₂:J→Credit)(L M:Credit)(rate:J→J→Credit)(coins:Prices)
      (A:(s:J)→types s→Alma (R.family.labels.level (l s))→ℝ),
      (∀s i h,0 ≤ A s i h) ∧ ∀ᶠ j:ℕ in atTop,
        ∃(W:ChorusLine (hol G) S p e C C C)(Y:Torch (hol G) S p rails C C C)
          (port:(s:J)→Home R (Q s) (own s) j),
          W.arch=Y.L ∧ Y.L.V.draws=R.family.path.levels ∧ Y.L.V.paid=R.metals.O ∧
          Y.L.V.y=zz R.family.path.levels ∧ Y.L.V.anchor=j ∧
          FramesR (hol G) Y.L.V C C Q C ∧ HorizonP (hol G) Y.L.V C C Q ∧
          (∀s t,WilsonIndependentConditionedGramCampus.Paid Y.L.V (Q s) (Q t) k (rate s t)) ∧
          ∀(host m f K N per target:ℕ),j ≤ host → host ≤ m → m ≤ f → ∀(up:f ≤ K)(live:K ≤ N)(η:ℝ),0 ≤ η → ∀
          (arms:(s:J)→ι s→Resident R (l s) f K N per target up live η),
            let δ:=R.family.S.a K/R.family.S.a m
            let term:=(fun s (i:types s)=>rehome (arms s i.1) m (plain s i.1) i.2)
            let ward:=(fun s (i:types s)=>plate (sectionAt R I (survey s i.1) (l s)) (admit s))
            let F:=(fun s (i:types s)=>charge e (term s i) (A s i))
            (∀s (i:types s),let X:=arms s i.1;let Fₛ:=R.family.labels.level (l s)
              Shrine (ward s i) (term s i)=δ^(l s) • Shrine (ward s i) (offered Fₛ (plain s i.1) i.2 (raw X)) ∧
              F s i=δ^(l s)*charge e (offered Fₛ (plain s i.1) i.2 (raw X)) (A s i) ∧
              F s i ≤ restored (e:=e) (A s i) X*δ^(-η)) ∧
            ∃T:Assigned R Q own Y.L.V coins j port types
                (fun s i=>Shrine (ward s i) (term s i)) F u b host m K N,
              Enrolled T L M ∧ Earned T C₁ C₂ (rate 0 1) L M:=by
  classical
  intro Q S types
  obtain ⟨C₁,C₂,L,M,rate,coins,A,nn,receipt⟩:=
    WilsonIndependentConditionedBankOpening.original R simple v funded p rails l d admit own b
      reserve depth I types (fun s i=>survey s i.1)
  refine ⟨C₁,C₂,L,M,rate,coins,A,nn,?_⟩
  filter_upwards [receipt] with j date
  obtain ⟨W,Y,port,coarse,old,clock,shape,anchor,frames,roof,grams,sold⟩:=date
  refine ⟨W,Y,port,coarse,old,clock,shape,anchor,frames,roof,grams,?_⟩
  intro host m f K N per target start older before up live η et arms δ term ward F
  refine ⟨?_,sold host m K N start older (before.trans up) live term⟩
  intro s i
  have exactWord:=WilsonIndependentConditionedBankRulerPorts.original (e:=e) (arms s i.1) m I
    (survey s i.1) (plain s i.1) i.2 (admit s) (A s i) (nn s i)
  have pay:=(WilsonIndependentConditionedBankSeats.paid (e:=e) (arms s i.1) I (survey s i.1) (admit s)
    (A s i) (nn s i) i.2).2.2
  exact ⟨exactWord.1,exactWord.2,WilsonIndependentConditionedBankRulerPorts.received (arms s i.1)
    before et (plain s i.1) i.2 e (A s i) (nn s i) pay⟩

end YM.Integration.WilsonIndependentConditionedBankRulerSchool
