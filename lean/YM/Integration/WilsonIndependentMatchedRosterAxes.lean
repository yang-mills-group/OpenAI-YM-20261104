import YM.Integration.WilsonIndependentMatchedRosterWages
import YM.Integration.WilsonIndependentMatchedRosterPlanted

/-! Basis directions at the receiving scale are priced separately from
the measured numerical coefficients which multiply them. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterAxes
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterChronology (mass born)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMatchedRosterPowers (profiles)
variable {G:Gauge}{h D k e u₀ n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}{dim:Fin (n+1)→ℕ}

open WilsonIndependentEvenPassport (old count)
open WilsonIndependentMatchedRosterReception (bill)

open WilsonIndependentMatchedRosterStop (Hearing)
open WilsonIndependentMatchedRosterSlots (degree entry wallet)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedCutBudget (restored)
open WilsonIndependentEvenPassport (young)

open WilsonIndependentMatchedRosterPool (Billed)
open WilsonIndependentMatchedRosterCuts (ranks counts)
open WilsonIndependentMatchedRosterReception (perSite)
open WilsonIndependentMatchedRosterWages (geo)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedPivotSeat (axis ticket)
open WilsonIndependentMatchedProxyIncome (tariff)
open private speed pos scale from YM.Integration.WilsonOriginalPublicPlantedPeriod

def source (flag:Bool)(a rent:ℝ):ℝ:=if flag then |a| * rent else 1

private lemma below (run:XSpace.Run)(idx:ℕ):(run.step idx).spacing ≤ 1:=by
  apply (Real.log_nonpos_iff (run.step idx).positive.le).mp
  rw [scale]
  exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg idx) (pos run).le)

/-- A fixed basis probe at a receiving coordinate, with its actual thermal
grade. An arbitrary number of designated residuals can accompany it on
the same matched course. Unmarked peers have unit income here. -/
theorem original (run:XSpace.Run)(base u b:ℕ)(cap η:ℝ)(small:0<η):
    ∀ᶠidx:ℕ in atTop,∀(n:ℕ)(L:Torch H T p v E W K)(X:Fin (n+1)→CutsP H T p v E W K U)(f:ℕ)
      (φ:Fin (n+1)→Rarity D)(flag:Fin (n+1)→Bool)(a amp rent B:Fin (n+1)→ℝ)
      (axisName:Fin (n+1)→Alma F)(q:Fin (n+1)→ℕ)(stem:Fin (n+1)→TowerS G D)
      (y t z:ℝ)(o:CellR),
      let δ:=(run.step idx).spacing
      let l:=fun s=>degree (flag s) k h
      let M:=fun s=>source (flag s) (a s) (rent s)
      let c:=fun s=>axis (axisName s) (q s)
      let fields:=fun s=>entry (flag s) (X s) (a s/amp s) (c s) (φ s) y o
      (∀s,Filed (X s) L run base idx f (amp s) δ η (rent s) (stem s))→
      (∀j ≤ old run base idx,L.L.V.y (f+j) ≤ cap)→(∀s,q s ≤ e)→0<t→0 ≤ z→
      (∀s,0 ≤ rent s)→(∀s,0 ≤ B s)→Billed run base idx flag u b η X f φ a amp rent B c y t z o→
      ∀stop ≤ old run base idx,Hearing (X 0) (ranks flag k h) u ((X 0).m+(X 0).i) (f+stop)
        (mass fields (X 0).i) (geo n e u b l t z*perSite u b z M B*
         δ^((counts flag:ℝ)/4-((n+3:ℕ):ℝ)*η)):=by
  let C:=tariff H T p e u b E W U
  filter_upwards [WilsonOriginalPublicPlantedStableCredit.credit (H:=H) (T:=T) (p:=p) (v:=v)
    (E:=E) (W:=W) (K:=K) (U:=U) run C cap η small]
    with idx price n L X f φ flag a amp rent B name q stem y t z o δ l M c fields filed ages grade ht hz hM hB enrolled stop older
  have positive:0<δ:=(run.step idx).positive
  let A:=fun s=>wallet (flag s) (X s) (c s) (|a s| * (δ^(-η)*rent s)) u b
  have loc (s:Fin (n+1)):(X s).vesselsC.y (X s).m ≤ cap:=by
    have same:(X s).vesselsC=L.L.V:=congrArg (fun a=>a.L.V) (filed s).school
    rw [same,(filed s).report];exact ages _ le_rfl
  have earned (s:Fin (n+1)):C.buy (X s).Age ≤ δ^(-η):=price (X s) (loc s) (filed s).scale
  have income (s:Fin (n+1)):0 ≤ M s:=by dsimp only [M,source];split <;> first | positivity | exact mul_nonneg (abs_nonneg _) (hM _)
  have p (s:Fin (n+1)):0 ≤ A s:=by
    dsimp only [A,wallet];split
    · exact mul_nonneg (abs_nonneg _) (mul_nonneg (Real.rpow_nonneg positive.le _) (hM _))
    · rw [show c s=axis (name s) (q s) from rfl,ticket _ _ (grade s),mul_one]
      exact zero_le_one.trans (C.purchase (X s).windowC.warm)
  have pay (s:Fin (n+1)):A s ≤ δ^(-η)*M s:=by
    dsimp only [A,M,source,wallet]
    cases flag s
    · change C.buy (X s).Age * WilsonIndependentMatchedProxyIncome.cost e (axis (name s) (q s)) ≤ δ^(-η)*1
      rw [ticket _ _ (grade s),mul_one,mul_one]
      exact earned s
    · exact le_of_eq (by change |a s| * (δ^(-η)*rent s)=δ^(-η)*(|a s| * rent s);ring)
  have bound:=WilsonIndependentMatchedRosterWages.combined l e u b (counts flag) δ η t z A M B positive
    (below run idx) small.le ht hz income p hB pay
  have H₀:=enrolled stop older
  exact ⟨⟨H₀.1.1.trans bound,fun j hj r hr=>(H₀.1.2 j hj r hr).more bound⟩,fun j hj w=>(H₀.2 j hj w).trans bound⟩

end YM.Integration.WilsonIndependentMatchedRosterAxes
