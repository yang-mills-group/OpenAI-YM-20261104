import YM.Integration.WilsonIndependentConditionedBankShellPrice

/-! Source homogeneity of the original conditioned shell price. The two
summands of the signed local estimate share the same rooted input fee. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramHomogeneity
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentMatchedRosterMasks (Bits choose)
open WilsonIndependentMatchedRosterReception (perSite)
open WilsonIndependentMatchedRosterPowers (profiles)
open WilsonIndependentConditionedBankShellPrice (wage)
open WilsonIndependentConditionedLocalRate (fee)
open WilsonIndependentMatchedProxyIncome (tariff)
open WilsonIndependentConditionedBankFittedFees (age)
open scoped BigOperators Topology Classical
local notation "J" => Fin 2
local notation "C" => Credit.leanC
variable {G:Gauge}{n:ℕ}

theorem receipt (k e u b:ℕ)(l:Fin (n+1)→ℕ)(t z:ℝ)(A B S:Fin (n+1)→ℝ)(budget height ζ:ℝ):
    fee k e u b l t z (fun s=>A s*S s) B budget height ζ =
      fee k e u b l t z A B budget height ζ*(∏s,S s):=by
  have single:perSite u b z (fun s=>A s*S s) B=perSite u b z A B*(∏s,S s):=by
    unfold perSite
    rw [←Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _=>by ring
  unfold fee
  rw [single]
  unfold profiles
  ring

def paid (mask:Bits 1)(a A:J→ℝ):ℝ:=∏s,if choose 1 mask s then |a s| *A s else 1

theorem touched (mask:Bits 1)(a A:J→ℝ):
    paid mask a A=∏s ∈ univ.filter (fun s=>choose 1 mask s=true),|a s| *A s:=by
  simp only [paid,Finset.prod_filter]

theorem original (R:Run G)(Q:J→SealR G)(coins:Prices)(k e u b host m K:ℕ)
    (ζ:ℝ)(a A B:J→ℝ)(t z:ℝ)(mask:Bits 1):
    wage (k:=k) (e:=e) R Q coins u b host m K ζ a A B t z mask=
      wage (k:=k) (e:=e) R Q coins u b host m K ζ (fun _=>1) (fun _=>1) B t z mask*paid mask a A:=by
  let S:=fun i=>if choose 1 mask i then |a i| *A i else 1
  let basis:=fun i=>if choose 1 mask i then (coins.slot mask i).buy (age R m K)
    else (tariff (hol G) (Q i).ans (Q i).path e u b C C C).buy (age R m K)
  have fees:(fun i=>if choose 1 mask i then (coins.slot mask i).buy (age R m K)*(|a i| *A i)
        else (tariff (hol G) (Q i).ans (Q i).path e u b C C C).buy (age R m K))=
      fun i=>basis i*S i:=by
    funext i
    cases hit:choose 1 mask i <;> simp [S,basis,hit]
  simp only [wage,abs_one,mul_one,fees]
  rw [receipt]
  exact (mul_assoc _ _ _).symm

end YM.Integration.WilsonIndependentConditionedGramHomogeneity
