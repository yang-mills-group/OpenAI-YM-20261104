import YM.Integration.WilsonIndependentConditionedActualFare
import YM.Integration.WilsonIndependentConditionedGramSplitReceiving

/-! The two original home fees at the common optical target, before the separate physical powers of the reporting clock. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedActualSplit
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

def inverse (R:Run G)(L M:Credit)(f:ℕ):ℝ:=
 (1+|L.buy (zz R.family.path.levels f)|)*(1+|M.buy (zz R.family.path.levels f)|)

theorem booked (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(T:ℕ)(L M:Credit):
    Pay R (inverse R L M):=by
  have term (c:Credit):Pay R (fun f=>1+|c.buy (zz R.family.path.levels f)|):=by
    exact (Pay.fixed R 1).add (by simpa only [WilsonIndependentConditionedActualCredit.homes] using
      (ages R simple slow T c).1.abs)
  exact (term L).mul (term M)

theorem polynomial (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    {ι:Type*}(choose:J→ι)(d:ι→Fin (D+1))(M:ι→ℝ)(c:J→ℝ)(mass:∀s,0 ≤ M (choose s))(coin:∀s,0 ≤ c s)
    (Q:J→SealR G)(C₁ C₂:J→Credit)(rate L M':Credit)(coins:Prices)(u b T q:ℕ)(ζ:ℝ)(B:J→ℝ)(t z:ℝ):
    ∃P:Credit,∀ᶠ f:ℕ in atTop,
      let K:=berth R T f
      let cap:=fun s=>M (choose s)*fixed R (d (choose s)).val*c s
      let U:=roof (wage (k:=k) (e:=e) R Q coins u b f f K ζ (fun _=>1) (fun _=>1) B t z)
      let F:=fun s=>|field R (Q s) (C₁ s) (C₂ s) f f K q 1 1|
      homeLow q U (inverse R L M' f) cap ≤ P.buy (badge R f) ∧
        ∀(φ:(s:J)→Rarity (Q s).D)(y:ℝ),(∀s,radiusH (φ s) 1 y ≤ z) →
          homeHigh q U F cap |gram (e:=e) R Q rate f K q φ B y| ≤ P.buy (badge R f):=by
  let cap:=fun s=>M (choose s)*fixed R (d (choose s)).val*c s
  let U:=fun f=>roof (wage (k:=k) (e:=e) R Q coins u b f f (berth R T f) ζ (fun _=>1) (fun _=>1) B t z)
  let F:=fun f s=>|field R (Q s) (C₁ s) (C₂ s) f f (berth R T f) q 1 1|
  let V:=fun f=>|quote (e:=e) R Q rate f (berth R T f) q B z|
  let lo:=fun f=>homeLow q (U f) (inverse R L M' f) cap
  let hi:=fun f=>homeHigh q (U f) (F f) cap (V f)
  have c0 (s:J):0 ≤ cap s:=mul_nonneg (mul_nonneg (mass s)
    (WilsonIndependentConditionedGramRawHome.fixed_nonnegative R _)) (coin s)
  have uu:=unitWage (k:=k) (e:=e) R simple slow Q coins u b T ζ B t z
  have ff (s:J):Pay R (fun f=>F f s*cap s):=
    (stripped R simple slow (Q s) (C₁ s) (C₂ s) T q).abs.mul (Pay.fixed R _)
  have vv:= (gramWage (e:=e) R simple slow Q rate T q B z).abs
  have ucap:= (uu.mul (Pay.fixed R (1+cap 0))).mul (Pay.fixed R (1+cap 1))
  have pl:Pay R lo:=((Pay.fixed R ((q+1:ℕ):ℝ)).mul ucap).mul (booked R simple slow T L M')
  have ph:Pay R hi:=(((Pay.fixed R (2*((q+1:ℕ):ℝ))).mul ucap).mul ((ff 0).add (ff 1))).add
    ((((Pay.fixed R 3).mul vv).mul (ff 0)).mul (ff 1))
  obtain ⟨P,pay⟩:=pl.max ph
  refine ⟨P,?_⟩
  have hot:=(tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)).eventually_ge_atTop 1
  filter_upwards [pay,hot] with f amount one
  have bound: max (lo f) (hi f) ≤ P.buy (badge R f):=(le_abs_self _).trans (amount one)
  refine ⟨(le_max_left ..).trans bound,?_⟩
  intro φ y room
  have gv:|gram (e:=e) R Q rate f (berth R T f) q φ B y| ≤ V f:=
    (WilsonIndependentConditionedActualWages.profiles (e:=e) R Q rate f (berth R T f) q B z φ y room).trans (le_abs_self _)
  have cf (s:J):0 ≤ F f s*cap s:=mul_nonneg (abs_nonneg _) (c0 s)
  apply le_trans _ ((le_max_right ..).trans bound)
  change _ ≤ homeHigh q (U f) (F f) cap (V f)
  unfold homeHigh
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left gv (by norm_num:0≤(3:ℝ))) (cf 0)) (cf 1))

theorem original (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    {ι:Type*}(choose:J→ι)(d:ι→Fin (D+1))(M:ι→ℝ)(c:J→ℝ)(mass:∀s,0 ≤ M (choose s))(coin:∀s,0 ≤ c s)
    (Q:J→SealR G)(C₁ C₂:J→Credit)(rate L M':Credit)(coins:Prices)(u b T q:ℕ)(ζ:ℝ)(B:J→ℝ)(t z:ℝ)
    {ε:ℝ}(ep:0<ε):
    ∀ᶠ f:ℕ in atTop,
      let K:=berth R T f
      let cap:=fun s=>M (choose s)*fixed R (d (choose s)).val*c s
      let U:=roof (wage (k:=k) (e:=e) R Q coins u b f f K ζ (fun _=>1) (fun _=>1) B t z)
      let F:=fun s=>|field R (Q s) (C₁ s) (C₂ s) f f K q 1 1|
      homeLow q U (inverse R L M' f) cap ≤ (thermal R f)^(-ε) ∧
        ∀(φ:(s:J)→Rarity (Q s).D)(y:ℝ),(∀s,radiusH (φ s) 1 y ≤ z) →
          homeHigh q U F cap |gram (e:=e) R Q rate f K q φ B y| ≤ (thermal R f)^(-ε):=by
  obtain ⟨P,p⟩:=polynomial (k:=k) (e:=e) R simple slow choose d M c mass coin Q C₁ C₂ rate L M' coins
    u b T q ζ B t z
  filter_upwards [p,WilsonIndependentConditionedActualCredit.subpower R simple P ep] with f bound pay
  exact ⟨bound.1.trans pay,fun φ y room=>(bound.2 φ y room).trans pay⟩

end YM.Integration.WilsonIndependentConditionedActualSplit
