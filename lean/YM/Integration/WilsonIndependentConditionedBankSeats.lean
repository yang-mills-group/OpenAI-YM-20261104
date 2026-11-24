import YM.Integration.WilsonIndependentConditionedBankOpening
import YM.Integration.WilsonIndependentNotebookRawInvoice

/-! Each preparation chooses one true measured resident for its two real components. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankSeats
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

open WilsonIndependentNotebookConstantSeat (issue seat)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonAddressedTrialPivotUnits (row)
open WilsonIndependentConditionedBankRawUnits (home)

structure Resident (R:Run G)(d f K N p target:ℕ)(up:f ≤ K)(live:K ≤ N)(η:ℝ) where
  station : ℕ
  before : station ≤ f
  axis : (R.family.label d)≃ₗ[ℂ]R.family.label d
  source : R.family.label d
  salary : ℝ
  paid : Cash (R:=R) d station f K N p target before up live η axis source salary
  arm : Arm R d N p f K
  same : arm.w=axis.symm (fitted R d station N p source)
  phase : ℂ

variable {R:Run G}{d f K N p target:ℕ}{up:f ≤ K}{live:K ≤ N}{η:ℝ}
local notation "F" => R.family.labels.level d

def raw (v:Resident R d f K N p target up live η):(F).Coeff:=
  row R d K N p v.phase (coords R v.arm)

def submitted (v:Resident R d f K N p target up live η)(im:Bool):Verse F:=
  issue F im (((R.family.S.a K/R.family.S.a f)^d) • raw v)

def restored (A:Alma F→ℝ)(v:Resident R d f K N p target up live η):ℝ:=
  ((e+1:ℕ):ℝ)*(∑i:(F).Index,A (seat F i))*home R d v.station f η v.phase v.salary

theorem paid (v:Resident R d f K N p target up live η)(I:Initialize G)(survey:Bool)(fit:d<D)
    (A:Alma F→ℝ)(nn:∀i,0 ≤ A i)(im:Bool):
    let δ:=R.family.S.a K/R.family.S.a f
    let T:=sectionAt R I survey d
    Shrine (plate T fit) (submitted v im)=δ^d • Shrine (plate T fit) (issue F im (raw v)) ∧
    charge e (submitted v im) A=δ^d*charge e (issue F im (raw v)) A ∧
    charge e (submitted v im) A ≤ restored (e:=e) A v*δ^(-η):=by
  intro δ T
  obtain ⟨whole,exactPrice,fare⟩:=WilsonIndependentNotebookRawInvoice.original R I survey fit e A nn
    v.before up live v.axis v.source v.paid v.arm v.same v.phase im
  refine ⟨whole,exactPrice,fare.trans_eq ?_⟩
  dsimp only [restored]
  ring

end YM.Integration.WilsonIndependentConditionedBankSeats
