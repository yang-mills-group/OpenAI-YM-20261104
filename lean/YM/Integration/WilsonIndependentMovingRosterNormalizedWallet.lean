import YM.Integration.WilsonIndependentMatchedRosterSlots

/-! Whole submitted coordinates at the actual report, with the stable fee
only on those arms selected as stable. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedWallet
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonIndependentMatchedProxyIncome (cost tariff)
open WilsonIndependentMatchedRosterSlots (wallet)
open scoped BigOperators Classical
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
  {v:Rails h k u₀ e}{E W K U:Credit}{I:Type}[Fintype I]

def amount (flag:Bool)(e:ℕ)(c:Verse F)(fee:ℝ):ℝ:=if flag then fee else cost e c

def rent (H:Hol G)(T:SectionData F)(p:h<D)(e u b:ℕ)(E W U stable:Credit):Credit:=
  stable.prodC (tariff H T p e u b E W U)

theorem one (X:CutsP H T p v E W K U)(c:Verse F)(stable:Credit)(fee:ℝ)(paid:0 ≤ fee)
    (flag:Bool)(u b:ℕ):
    wallet flag X c (stable.buy X.Age*fee) u b ≤
      (rent H T p e u b E W U stable).buy X.Age*amount flag e c fee:=by
  let S:=tariff H T p e u b E W U
  have st:1 ≤ stable.buy X.Age:=stable.purchase X.windowC.warm
  have hr:1 ≤ S.buy X.Age:=S.purchase X.windowC.warm
  have both:(rent H T p e u b E W U stable).buy X.Age=stable.buy X.Age*S.buy X.Age:=Credit.products ..
  cases flag with
  | true =>
    simpa only [wallet,amount,if_true,both] using
      (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (zero_le_one.trans st) hr) paid)
  | false =>
    simpa only [wallet,amount,Bool.false_eq_true,if_false,both,S] using
      (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (zero_le_one.trans hr) st)
        (WilsonIndependentMatchedProxyIncome.nn c))

theorem roster (X:I→CutsP H T p v E W K U)(c:I→Verse F)(stable:I→Credit)(fee:I→ℝ)
    (nn:∀i,0 ≤ fee i)(flag:I→Bool)(u b:ℕ)(net paid:ℝ)(positive:0 ≤ net)
    (finance:net*(∏i,(rent H T p e u b E W U (stable i)).buy (X i).Age) ≤ paid):
    net*(∏i,wallet (flag i) (X i) (c i) ((stable i).buy (X i).Age*fee i) u b) ≤
      paid*(∏i,amount (flag i) e (c i) (fee i)):=by
  have pos(i:I):0 ≤ wallet (flag i) (X i) (c i) ((stable i).buy (X i).Age*fee i) u b:=
    WilsonIndependentMatchedRosterSlots.money _ _ _ (mul_nonneg (zero_le_one.trans
      ((stable i).purchase (X i).windowC.warm)) (nn i)) _ _
  have gross(i:I):0 ≤ amount (flag i) e (c i) (fee i):=by
    unfold amount
    split
    · exact nn _
    · exact WilsonIndependentMatchedProxyIncome.nn _
  let r (i:I):=(rent H T p e u b E W U (stable i)).buy (X i).Age
  let a (i:I):=amount (flag i) e (c i) (fee i)
  calc
    _≤net*(∏i,r i*a i):=mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=>pos i)
      (fun i _=>one (X i) (c i) (stable i) (fee i) (nn i) (flag i) u b)) positive
    _=(net*∏i,r i)*(∏i,a i):=by rw [Finset.prod_mul_distrib,mul_assoc]
    _≤paid*(∏i,a i):=mul_le_mul_of_nonneg_right finance (Finset.prod_nonneg fun i _=>gross i)

end YM.Integration.WilsonIndependentMovingRosterNormalizedWallet

