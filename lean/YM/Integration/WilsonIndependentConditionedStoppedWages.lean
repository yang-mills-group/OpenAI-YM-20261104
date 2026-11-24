import YM.Integration.WilsonIndependentConditionedStoppedRoom
import YM.Integration.WilsonIndependentConditionedEarlierWages
import YM.Integration.WilsonIndependentConditionedActualWages

/-! Polynomial cost at an earlier home, with unrestricted numerical radius, inverse clearance and amplitudes. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedStoppedWages
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


open WilsonIndependentConditionedActualBudget (Pay ages)
open WilsonIndependentConditionedActualCredit (badge gramAge)
open WilsonIndependentConditionedBankFittedFees (age)
open WilsonIndependentConditionedBankShellPrice (wage)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentConditionedBankApplied (field gram)
open WilsonIndependentConditionedGramPrices (profile)
open WilsonIndependentMatchedRosterReception (perSite)
open WilsonIndependentMatchedProxyIncome (tariff)
open WilsonIndependentMatchedRosterMasks (Bits choose)
open WilsonIndependentMatchedRosterSlots (degree)
open WilsonInvariantActionPosition (berth)
open Real


open WilsonIndependentConditionedStoppedRoom (Room)
open WilsonIndependentConditionedProfileCredit (Paid)
open WilsonIndependentConditionedProfileCredit.Paid
abbrev Cost {R:Run G}{T U:ℕ}(F:Room R T U→ℝ):Prop:=Paid Room.bill F

theorem branch (R:Run G)(Q:J→SealR G)(coins:Prices)(u b T U:ℕ)(ζ:ℝ)(mask:Bits 1):
    Cost (fun X:Room R T U=>wage (k:=k) (e:=e) R Q coins u b X.v X.m X.K ζ (fun _=>1)
      (fun _=>1) X.B X.t X.z mask):=by
  let idle:Credit:=⟨0,1,le_rfl⟩
  let blank:Prices:={coins with stop:=fun _=>idle}
  have source:=Room.registered (WilsonIndependentConditionedEarlierWages.branch (k:=k) (e:=e) R Q blank u b T U ζ mask)
  have refund:=(Room.ages R T U (coins.stop mask)).1.mul source
  simpa only [wage,blank,idle,Credit.buy,pow_zero,mul_one,one_mul] using refund

theorem unit (R:Run G)(Q:J→SealR G)(coins:Prices)(u b T U:ℕ)(ζ:ℝ):
    Cost (fun X:Room R T U=>roof (wage (k:=k) (e:=e) R Q coins u b X.v X.m X.K ζ
      (fun _=>1) (fun _=>1) X.B X.t X.z)):=by
  have cover:=branch (k:=k) (e:=e) R Q coins u b T U ζ
  exact (Paid.fixed _ 0).max ((cover (true,true)).max ((cover (true,false)).max (cover (false,true))))

theorem stripped (R:Run G)(Q:SealR G)(c d:Credit)(T U q:ℕ):
    Cost (fun X:Room R T U=>field R Q c d X.v X.m X.K q 1 1):=
  (Paid.fixed _ _).mul ((Room.ages R T U c).1.mul ((Room.ages R T U d).2.1.mul (Paid.fixed _ _)))

theorem gramWage (R:Run G)(Q:J→SealR G)(rate:Credit)(T U q:ℕ):
    Cost (fun X:Room R T U=>WilsonIndependentConditionedActualWages.quote (e:=e) R Q rate X.v X.K q X.B X.z):=by
  obtain ⟨_,z,B⟩:=Room.shapes (R:=R) (T:=T) (U:=U)
  have tile (s:J):Cost (fun X:Room R T U=>WilsonIndependentConditionedActualWages.tile X.z (X.B s)):=
    (((Paid.fixed _ 5).mul z).pow 4).mul (B s).abs
  exact (Paid.fixed _ _).mul (((Room.ages R T U rate).2.2.abs).mul
    (((Paid.fixed _ _).mul (tile 0)).mul (tile 1)))

end YM.Integration.WilsonIndependentConditionedStoppedWages
