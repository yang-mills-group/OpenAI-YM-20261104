import YM.Integration.WilsonIndependentMovingRosterNormalizedPortfolio

/-! Discharge the actual largest dated invoice together with its signed incoming appointments. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedEarnings

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterTariff (factor)
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentMovingRosterLaneFilm (Licensed)
open WilsonIndependentMatchedRosterPowers (profiles)
open WilsonIndependentMatchedRosterSlots (degree count entry wallet)
open WilsonIndependentMatchedRosterMasks (Bits choose placed)
open WilsonIndependentMatchedRosterCuts (counts ranks)
open WilsonIndependentMovingRosterTopFields (stable fitted)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedRosterMasks (quiet present)
open WilsonIndependentMatchedCoverDate (age)
variable {G:Gauge}{H:Hol G}{n e h D k u₀:ℕ}{F:Labels.Frame G h}{T:SectionData F}
    {p:h<D}{v:Rails h k u₀ e}{E W K U:Credit}


def edge (R:Realm G (e+1) E)(C S:Credit)(d m j:ℕ):ℝ:=
  C.buy (age R m j)*R.cash S j*((ll R.draws j).L.val:ℝ)^d

lemma wealth (R:Realm G (e+1) E)(C S:Credit)(d:ℕ){m j:ℕ}(live:R.anchor ≤ m)(later:m ≤ j):
    1 ≤ edge R C S d m j:=by
  have time:1 ≤ WilsonIndependentMatchedCoverDate.age R m j:=by
    have early:=R.depth m live
    have days:=scales R.draws.S later
    have count:0 ≤ ((j-m:ℕ):ℝ):=by positivity
    unfold WilsonIndependentMatchedCoverDate.age
    linarith
  have coins:1 ≤ R.cash S j:=S.purchase (R.depth j (live.trans later))
  have block:1 ≤ ((ll R.draws j).L.val:ℝ):=by exact_mod_cast (ll R.draws j).L.pos
  have pow:1 ≤ ((ll R.draws j).L.val:ℝ)^d:=one_le_pow₀ block
  unfold edge
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (C.purchase time) coins) pow

theorem maximum (c:ℕ→ℝ){m N:ℕ}(live:m ≤ N):
    ∃j,m ≤ j ∧ j ≤ N ∧ ∀i,m ≤ i → i ≤ N → c i ≤ c j:=by
  obtain ⟨j,hj,pay⟩:=Finset.exists_max_image (Finset.Icc m N) c ⟨m,Finset.mem_Icc.mpr ⟨le_rfl,live⟩⟩
  exact ⟨j,(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2,fun i hi hn=>pay i (Finset.mem_Icc.mpr ⟨hi,hn⟩)⟩

def contract (n k out e u b h:ℕ)(mask:Bits (n+1))(gap z zoom:ℝ)(B:Fin ((n+1)+1)→ℝ):ℝ:=
  let l:=ranks (choose (n+1) mask) k h
  let testing:=∏s,factor u b z*B s
  (zoom^(h+u)*(coinMat l e)^(n+1)+2*(zoom^(h+u+u)*profiles (n+1) out e u b gap z 1))*testing

theorem booked (mask:Bits (n+1))(R:Realm G (e+1) E)(X:Fin ((n+1)+1)→CutsP H T p v E W K U)
    (col:Fin ((n+1)+1)→Verse F)(A B:Fin ((n+1)+1)→ℝ)(L:Credit)(out u b older m:ℕ)(gap z zoom budget cap:ℝ)
    (house:0 ≤ z)(apart:0 < gap)(forward:0 ≤ zoom)(paid:∀s,0 ≤ B s)
    (fund:∀s,0 ≤ wallet (choose (n+1) mask s) (X s) (col s) (A s) u b)
    (time:1 ≤ L.buy (age R older m))(income:1 ≤ budget)
    (whole:L.buy (age R older m)*budget*∏s,wallet (choose (n+1) mask s) (X s) (col s) (A s) u b ≤ cap):
    WilsonIndependentMovingRosterNormalizedPortfolio.rate mask R X col A B L out u b older m gap z zoom budget ≤
      contract n k out e u b h mask gap z zoom B*cap:=by
  let rent:=fun s=>wallet (choose (n+1) mask s) (X s) (col s) (A s) u b
  let cash:=∏s,rent s
  let testing:=∏s,factor u b z*B s
  let dated:=L.buy (age R older m)
  let first:=zoom^(h+u)*(coinMat (ranks (choose (n+1) mask) k h) e)^(n+1)
  let joins:=2*(zoom^(h+u+u)*profiles (n+1) out e u b gap z 1)
  have sep:(∏s,factor u b z*(B s*rent s))=testing*cash:=by
    dsimp only [testing,cash]
    simp_rw [←mul_assoc]
    rw [Finset.prod_mul_distrib]
  have coins:0 ≤ cash:=Finset.prod_nonneg (fun s _=>fund s)
  have factor0:0 ≤ factor u b z:=by unfold WilsonIndependentMatchedRosterTariff.factor;positivity
  have tests:0 ≤ testing:=Finset.prod_nonneg (fun s _=>mul_nonneg factor0 (paid s))
  have old0:0 ≤ dated:=zero_le_one.trans time
  have first0:0 ≤ first:=mul_nonneg (pow_nonneg forward _) (pow_nonneg (coinMat_nn ..) _)
  have joins0:0 ≤ joins:=by
    dsimp only [joins,WilsonIndependentMatchedRosterPowers.profiles]
    have hard:=coinMat_nn out e
    positivity
  have joint:dated*budget*cash ≤ cap:=whole
  have own:dated*cash ≤ cap:=(mul_le_mul_of_nonneg_right (le_mul_of_one_le_right old0 income) coins).trans joint
  have mass:WilsonIndependentMovingRosterNormalizedPortfolio.rate mask R X col A B L out u b older m gap z zoom budget=
      first*testing*(dated*cash) + joins*testing*(dated*budget*cash):=by
    unfold WilsonIndependentMovingRosterNormalizedPortfolio.rate
    change dated*(zoom^(h+u)*((coinMat _ e)^(n+1)*(∏s,factor u b z*(B s*rent s)))+
      2*(zoom^(h+u+u)*(budget*profiles (n+1) out e u b gap z (∏s,factor u b z*(B s*rent s)))))=_
    rw [sep]
    dsimp only [first,joins,WilsonIndependentMatchedRosterPowers.profiles]
    ring
  rw [mass]
  change _ ≤ (first+joins)*testing*cap
  calc
    _ ≤ first*testing*cap + joins*testing*cap:=add_le_add
      (mul_le_mul_of_nonneg_left own (mul_nonneg first0 tests))
      (mul_le_mul_of_nonneg_left joint (mul_nonneg joins0 tests))
    _ = _:=by ring

end YM.Integration.WilsonIndependentMovingRosterNormalizedEarnings
