import YM.Integration.WilsonIndependentConditionedEarlierRoom
import YM.Integration.WilsonIndependentConditionedActualWages

/-! Polynomial cost at an earlier home, with unrestricted numerical radius, inverse clearance and amplitudes. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedEarlierWages
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


open WilsonIndependentConditionedEarlierRoom (Room)
open WilsonIndependentConditionedProfileCredit (Paid)
open WilsonIndependentConditionedProfileCredit.Paid
abbrev Cost {R:Run G}{T U:ℕ}(F:Room R T U→ℝ):Prop:=Paid Room.bill F

private theorem localFee (R:Run G)(T U k e u b:ℕ)(l:J→ℕ)(A:J→Room R T U→ℝ)
    (budget:Room R T U→ℝ)(height ζ:ℝ)(paid:∀s,Cost (A s))(pb:Cost budget):
    Cost (fun X=>WilsonIndependentConditionedLocalRate.fee k e u b l X.t X.z (fun s=>A s X) X.B
      (budget X) height ζ):=by
  obtain ⟨pt,pz,pB⟩:=Room.shapes (R:=R) (T:=T) (U:=U)
  have pf:Cost (fun X:Room R T U=>WilsonIndependentMatchedRosterTariff.factor u b X.z):=
    (((Paid.fixed _ 5).mul pz).pow 4).mul ((Paid.fixed _ ((9:ℝ)^(u+b))).add
      (((Paid.fixed _ 1).add ((Paid.fixed _ 4).mul pz)).pow u))
  let Z (X:Room R T U):=perSite u b X.z (fun s=>A s X) X.B
  have zp:Cost Z:=Paid.products Finset.univ _
    (fun s=>pf.mul ((pB s).mul (paid s)))
  have ti:Cost (fun X:Room R T U=>(X.t^b)⁻¹):=by simpa only [inv_pow] using pt.pow b
  have front:Cost (fun X:Room R T U=>WilsonIndependentMatchedRosterPowers.profiles 1 k e u b X.t X.z (Z X)):=by
    simpa only [WilsonIndependentMatchedRosterPowers.profiles,Nat.cast_one] using ((((Paid.fixed Room.bill (1*(coinMat k e+1)^1)).mul ti).mul
    (((Paid.fixed _ 16).mul pz).pow u)).mul zp)
  exact ((Paid.fixed _ _).mul zp).add ((pb.mul front).mul (Paid.fixed _ _))

theorem branch (R:Run G)(Q:J→SealR G)(coins:Prices)(u b T U:ℕ)(ζ:ℝ)(mask:Bits 1):
    Cost (fun X:Room R T U=>wage (k:=k) (e:=e) R Q coins u b X.m X.m X.K ζ (fun _=>1)
      (fun _=>1) X.B X.t X.z mask):=by
  let d:=choose 1 mask
  let bills i (X:Room R T U):=if d i then (coins.slot mask i).buy (age R X.m X.K)*(|(1:ℝ)| *1)
      else (tariff (hol G) (Q i).ans (Q i).path e u b C C C).buy (age R X.m X.K)
  have tariffs (s:J):Cost (bills s):=by
    dsimp only [bills]
    split_ifs
    · exact (Room.ages R T U (coins.slot mask s)).2.1.mul (Paid.fixed _ _)
    · exact (Room.ages R T U _).2.1
  exact (Room.ages R T U (coins.stop mask)).1.mul
    (localFee R T U (2*k) e u b (fun i=>degree (d i) k (Q i).h) bills
      _ _ ζ tariffs (Room.ages R T U (coins.window mask)).2.1)

theorem unit (R:Run G)(Q:J→SealR G)(coins:Prices)(u b T U:ℕ)(ζ:ℝ):
    Cost (fun X:Room R T U=>roof (wage (k:=k) (e:=e) R Q coins u b X.m X.m X.K ζ
      (fun _=>1) (fun _=>1) X.B X.t X.z)):=by
  have cover:=branch (k:=k) (e:=e) R Q coins u b T U ζ
  exact (Paid.fixed _ 0).max ((cover (true,true)).max ((cover (true,false)).max (cover (false,true))))

theorem stripped (R:Run G)(Q:SealR G)(c d:Credit)(T U q:ℕ):
    Cost (fun X:Room R T U=>field R Q c d X.m X.m X.K q 1 1):=
  (Paid.fixed _ _).mul ((Room.ages R T U c).1.mul ((Room.ages R T U d).2.1.mul (Paid.fixed _ _)))

theorem gramWage (R:Run G)(Q:J→SealR G)(rate:Credit)(T U q:ℕ):
    Cost (fun X:Room R T U=>WilsonIndependentConditionedActualWages.quote (e:=e) R Q rate X.m X.K q X.B X.z):=by
  obtain ⟨_,z,B⟩:=Room.shapes (R:=R) (T:=T) (U:=U)
  have tile (s:J):Cost (fun X:Room R T U=>WilsonIndependentConditionedActualWages.tile X.z (X.B s)):=
    (((Paid.fixed _ 5).mul z).pow 4).mul (B s).abs
  exact (Paid.fixed _ _).mul (((Room.ages R T U rate).2.2.abs).mul
    (((Paid.fixed _ _).mul (tile 0)).mul (tile 1)))

end YM.Integration.WilsonIndependentConditionedEarlierWages
