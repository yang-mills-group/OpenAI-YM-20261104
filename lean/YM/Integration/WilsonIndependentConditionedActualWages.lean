import YM.Integration.WilsonIndependentConditionedActualBudget
import YM.Integration.WilsonIndependentConditionedBankApplied

/-! The unit shell, stripped field and Gram fees on a compact set of actual two-source test rooms. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedActualWages
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

private theorem localFee {n:ℕ}(R:Run G)(k e u b:ℕ)(l:Fin (n+1)→ℕ)(t z:ℝ)
    (A:Fin (n+1)→ℕ→ℝ)(B:Fin (n+1)→ℝ)(budget:ℕ→ℝ)(height ζ:ℝ)
    (paid:∀s,Pay R (A s))(pb:Pay R budget):
    Pay R (fun f=>WilsonIndependentConditionedLocalRate.fee k e u b l t z (fun s=>A s f) B
      (budget f) height ζ):=by
  let Z f:=perSite u b z (fun s=>A s f) B
  have zp:Pay R Z:=WilsonIndependentConditionedActualBudget.Pay.product Finset.univ _
    (fun s=>(Pay.fixed R (WilsonIndependentMatchedRosterTariff.factor u b z)).mul ((Pay.fixed R (B s)).mul (paid s)))
  exact ((Pay.fixed R _).mul zp).add
    ((pb.mul ((Pay.fixed R ((n:ℝ)*(coinMat k e+1)^n*(t^b)⁻¹*(16*z)^u)).mul zp)).mul (Pay.fixed R _))

theorem branch (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (Q:J→SealR G)(coins:Prices)(u b T:ℕ)(ζ:ℝ)(B:J→ℝ)(t z:ℝ)(mask:Bits 1):
    Pay R (fun f=>wage (k:=k) (e:=e) R Q coins u b f f (berth R T f) ζ (fun _=>1)
      (fun _=>1) B t z mask):=by
  let K f:=berth R T f
  let d:=choose 1 mask
  let bills i f:=if d i then (coins.slot mask i).buy (age R f (K f))*(|(1:ℝ)| *1)
      else (tariff (hol G) (Q i).ans (Q i).path e u b C C C).buy (age R f (K f))
  have tariffs (s:J):Pay R (bills s):=by
    dsimp only [bills]
    split_ifs
    · exact (ages R simple slow T (coins.slot mask s)).2.1.mul (Pay.fixed R _)
    · exact (ages R simple slow T _).2.1
  exact (ages R simple slow T (coins.stop mask)).1.mul
    (localFee R (2*k) e u b (fun i=>degree (d i) k (Q i).h) t z bills B
      _ _ ζ tariffs (ages R simple slow T (coins.window mask)).2.1)

theorem unitWage (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (Q:J→SealR G)(coins:Prices)(u b T:ℕ)(ζ:ℝ)(B:J→ℝ)(t z:ℝ):
    Pay R (fun f=>roof (wage (k:=k) (e:=e) R Q coins u b f f (berth R T f) ζ (fun _=>1)
      (fun _=>1) B t z)):=by
  have cover:=branch (k:=k) (e:=e) R simple slow Q coins u b T ζ B t z
  exact (Pay.fixed R 0).max ((cover (true,true)).max ((cover (true,false)).max (cover (false,true))))

theorem stripped (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (Q:SealR G)(c d:Credit)(T q:ℕ):
    Pay R (fun f=>field R Q c d f f (berth R T f) q 1 1):=by
  exact (Pay.fixed R _).mul ((ages R simple slow T c).1.mul
    ((ages R simple slow T d).2.1.mul (Pay.fixed R _)))

def tile (z B:ℝ):ℝ:=(5*z)^4*|B|
def quote (R:Run G)(Q:J→SealR G)(rate:Credit)(f K q:ℕ)(B:J→ℝ)(z:ℝ):ℝ:=
  ((q+1:ℕ):ℝ)*(|rate.buy (gramAge R f K)| *(|coinMat ((Q 0).h+(Q 1).h) e| *tile z (B 0)*tile z (B 1)))

private theorem fitted {a:ℕ}(φ:Rarity a)(z y B:ℝ)(h:radiusH φ 1 y ≤ z):
    |profile φ y B| ≤ tile z B:=by
  have rp:0 ≤ radiusH φ 1 y:=zero_le_one.trans (fieldCap φ 1 y)
  unfold WilsonIndependentConditionedGramPrices.profile tile
  rw [abs_mul,abs_of_nonneg (pow_nonneg (mul_nonneg (by norm_num:0≤(5:ℝ)) rp) 4)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg (by norm_num) rp) (mul_le_mul_of_nonneg_left h (by norm_num)) _) (abs_nonneg _)

theorem profiles (R:Run G)(Q:J→SealR G)(rate:Credit)(f K q:ℕ)(B:J→ℝ)(z:ℝ)
    (φ:(s:J)→Rarity (Q s).D)(y:ℝ)(room:∀s,radiusH (φ s) 1 y ≤ z):
    |gram (e:=e) R Q rate f K q φ B y| ≤ quote (e:=e) R Q rate f K q B z:=by
  have price:=fitted (φ 0) z y (B 0) (room 0)
  have ext:=fitted (φ 1) z y (B 1) (room 1)
  have tile0:0 ≤ tile z (B 0):=(abs_nonneg _).trans price
  simp only [WilsonIndependentConditionedBankApplied.gram,quote,gramAge,abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (q+1))]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul (mul_le_mul_of_nonneg_left price (abs_nonneg _)) ext (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) tile0)) (abs_nonneg _)) (Nat.cast_nonneg _)

theorem gramWage (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (Q:J→SealR G)(rate:Credit)(T q:ℕ)(B:J→ℝ)(z:ℝ):
    Pay R (fun f=>quote (e:=e) R Q rate f (berth R T f) q B z):=by
  exact (Pay.fixed R _).mul ((ages R simple slow T rate).2.2.abs.mul (Pay.fixed R _))

end YM.Integration.WilsonIndependentConditionedActualWages
