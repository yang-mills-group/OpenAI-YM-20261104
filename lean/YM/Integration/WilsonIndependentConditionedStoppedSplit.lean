import YM.Integration.WilsonIndependentConditionedStoppedWages
import YM.Integration.WilsonIndependentConditionedActualSplit

/-! The complete low and high original-profile tariffs on a genuine earlier home. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedStoppedSplit
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

open WilsonIndependentConditionedBankAward (fare)
open WilsonIndependentConditionedBankStableCost (gross)
open WilsonIndependentConditionedActualWages (unitWage stripped quote gramWage)

open WilsonIndependentConditionedGramSplitAward (homeLow homeHigh)
open WilsonIndependentConditionedGramRawHome (fixed)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)


open WilsonIndependentConditionedStoppedRoom (Room)
open WilsonIndependentConditionedProfileCredit (Paid)
open WilsonIndependentConditionedStoppedWages (Cost)
open WilsonIndependentConditionedActualSplit (inverse)

def Heard (R:Run G)(Q:J→SealR G)(C₁ C₂:J→Credit)(rate L M:Credit)(coins:Prices)
    (u b q host m K:ℕ)(ζ:ℝ)(H B:J→ℝ)(t z level:ℝ):Prop:=
  let U:=roof (wage (k:=k) (e:=e) R Q coins u b host m K ζ (fun _=>1) (fun _=>1) B t z)
  let F:=fun s=>|field R (Q s) (C₁ s) (C₂ s) host m K q 1 1|
  homeLow q U (inverse R L M m) H ≤ level ∧
    ∀(φ:(s:J)→Rarity (Q s).D)(y:ℝ),(∀s,radiusH (φ s) 1 y ≤ z) →
      homeHigh q U F H |gram (e:=e) R Q rate host K q φ B y| ≤ level

theorem room (R:Run G)(H:J→ℝ)(positive:∀s,0≤H s)
    (Q:J→SealR G)(C₁ C₂:J→Credit)(rate L M:Credit)(coins:Prices)(u b T U q:ℕ)(ζ:ℝ):
    ∃P:Credit,∀X:Room R T U,
      Heard (k:=k) (e:=e) R Q C₁ C₂ rate L M coins u b q X.v X.m X.K ζ H X.B X.t X.z (P.buy X.bill):=by
  let w:=fun X:Room R T U=>roof (wage (k:=k) (e:=e) R Q coins u b X.v X.m X.K ζ
    (fun _=>1) (fun _=>1) X.B X.t X.z)
  let F:=fun (X:Room R T U) s=>|field R (Q s) (C₁ s) (C₂ s) X.v X.m X.K q 1 1|
  let V:=fun X:Room R T U=>|quote (e:=e) R Q rate X.v X.K q X.B X.z|
  let lo:=fun X:Room R T U=>homeLow q (w X) (inverse R L M X.m) H
  let hi:=fun X:Room R T U=>homeHigh q (w X) (F X) H (V X)
  have uc:=WilsonIndependentConditionedStoppedWages.unit (k:=k) (e:=e) R Q coins u b T U ζ
  have fields (s:J):Cost (fun X=>F X s*H s):=
    (WilsonIndependentConditionedStoppedWages.stripped R (Q s) (C₁ s) (C₂ s) T U q).abs.mul (Paid.fixed _ _)
  have uv:Cost V:=(WilsonIndependentConditionedStoppedWages.gramWage (e:=e) R Q rate T U q).abs
  have inv (P:Credit):Cost (fun X:Room R T U=>1+|P.buy (zz R.family.path.levels X.m)|):=by
    exact (Paid.fixed _ 1).add (by simpa only [WilsonIndependentConditionedActualCredit.homes] using
      (Room.homeAge R T U P).abs)
  have ucap:= (uc.mul (Paid.fixed _ (1+H 0))).mul (Paid.fixed _ (1+H 1))
  have pl:Cost lo:=((Paid.fixed _ ((q+1:ℕ):ℝ)).mul ucap).mul ((inv L).mul (inv M))
  have ph:Cost hi:=(((Paid.fixed _ (2*((q+1:ℕ):ℝ))).mul ucap).mul ((fields 0).add (fields 1))).add
    ((((Paid.fixed _ 3).mul uv).mul (fields 0)).mul (fields 1))
  obtain ⟨P,pay⟩:=pl.max ph
  refine ⟨P,fun X=>?_⟩
  have bound: max (lo X) (hi X) ≤ P.buy X.bill:=(le_abs_self _).trans (pay X X.cap)
  refine ⟨(le_max_left ..).trans bound,?_⟩
  intro φ y room
  have gv:|gram (e:=e) R Q rate X.v X.K q φ X.B y| ≤ V X:=
    (WilsonIndependentConditionedActualWages.profiles (e:=e) R Q rate X.v X.K q X.B X.z φ y room).trans (le_abs_self _)
  have cf (s:J):0 ≤ F X s*H s:=mul_nonneg (abs_nonneg _) (positive s)
  apply le_trans _ ((le_max_right ..).trans bound)
  change _ ≤ homeHigh q (w X) (F X) H (V X)
  unfold homeHigh
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left gv (by norm_num:0≤(3:ℝ))) (cf 0)) (cf 1))

theorem original (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (H:J→ℝ)(positive:∀s,0≤H s)
    (Q:J→SealR G)(C₁ C₂:J→Credit)(rate L M:Credit)(coins:Prices)(u b T U q:ℕ)(ζ:ℝ):
    ∃P:Credit,∀ᶠ f:ℕ in atTop,∀{first v m:ℕ},first ≤ v → v ≤ m → m ≤ f →
      let K:=berth R T f
      R.family.S.scale K-R.family.S.scale first ≤ (U:ℝ)*(1+badge R v) →
      ∀(t z:ℝ)(B:J→ℝ),Heard (k:=k) (e:=e) R Q C₁ C₂ rate L M coins u b q v m K
        ζ H B t z (P.buy (WilsonIndependentConditionedEarlierRoom.Room.amount (badge R f) t z B)):=by
  obtain ⟨P,pay⟩:=room (k:=k) (e:=e) R H positive Q C₁ C₂ rate L M coins u b T (2*U) q ζ
  refine ⟨P,?_⟩
  filter_upwards [WilsonIndependentConditionedStoppedRoom.appoint R simple slow T U] with f sale
  intro first v m fv vm mf K span t z B
  obtain ⟨X,xf,xm,xv,xt,xz,xB⟩:=sale fv vm mf span t z B
  have income:=pay X
  change Heard (k:=k) (e:=e) R Q C₁ C₂ rate L M coins u b q X.v X.m (berth R T X.f)
    ζ H X.B X.t X.z (P.buy (WilsonIndependentConditionedEarlierRoom.Room.amount (badge R X.f) X.t X.z X.B)) at income
  simpa only [xf,xm,xv,xt,xz,xB] using income

end YM.Integration.WilsonIndependentConditionedStoppedSplit
