import YM.Integration.WilsonIndependentMatchedCoverCap
import YM.Integration.WilsonIndependentMovingRosterAllFineAge

/-! The date, original receiver and true block length spend one
polynomial credit on the actual enrolled calendar. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterMarginLedger
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonIndependentMatchedCoverDate (age)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e:ℕ}{E:Credit}

def market (C S E:Credit)(d:ℕ):Credit:=(C.prodC S).prodC (E.powC d)

theorem local_cost (R:Realm G (e+1) E)(C S:Credit)(d s m j N:ℕ)
    (live:R.anchor ≤ s)(home:s ≤ m)(edge:m ≤ j)(top:j ≤ N):
    C.buy (age R m j)*R.cash S j*((ll R.draws j).L.val:ℝ)^d ≤
      (market C S E d).buy (epoch R s N):=by
  let Z:=epoch R s N
  have homeLive:=live.trans home
  have warm:=R.depth m homeLive
  have spent:1 ≤ WilsonIndependentMatchedCoverDate.age R m j:=by
    unfold WilsonIndependentMatchedCoverDate.age
    linarith only [warm,scales R.draws.S edge,Nat.cast_nonneg (α:=ℝ) (j-m)]
  have cost:= (window R s m j live home edge).2.2.1
  have grow:epoch R s j ≤ Z:=by
    change R.y s+2*(R.draws.S.scale j-R.draws.S.scale s) ≤ R.y s+2*(R.draws.S.scale N-R.draws.S.scale s)
    linarith only [scales R.draws.S top]
  have jLive:=homeLive.trans edge
  have bound:=window R s j N live (home.trans edge) top
  have cf:=C.elder spent (cost.trans grow)
  have sf:=S.elder (R.depth j jLive) bound.2.1
  have length:=((R.taxes j jLive).height).trans (E.elder (R.depth j jLive) bound.2.1)
  rw [market,Credit.products,Credit.products,Credit.power]
  apply mul_le_mul _ (pow_le_pow_left₀ (by exact_mod_cast (ll R.draws j).L.pos.le) length d)
    (pow_nonneg (by positivity) _)
    (mul_nonneg (zero_le_one.trans (C.purchase bound.1)) (zero_le_one.trans (S.purchase bound.1)))
  exact mul_le_mul cf sf (zero_le_one.trans (S.purchase (R.depth j jLive))) (zero_le_one.trans (C.purchase bound.1))

/-- The full age of each named cut can spend that same common budget
even if its reporting date is different. -/
theorem source_age {h D k u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{W K U:Credit}(R:Realm G (e+1) E)(s N:ℕ)(live:R.anchor ≤ s)
    (X:CutsP H T p v E W K U)(same:X.vesselsC=R)(start:s ≤ X.m)(top:X.N=N)(ceiling:X.N=X.ceilC):
    1 ≤ X.Age ∧ X.Age ≤ epoch R s N:=by
  have finish:X.m+X.i=N:=ceiling.symm.trans top
  have fine:X.m ≤ N:=finish ▸ Nat.le_add_right _ _
  have site: X.Age=Compar R.draws.S R.y X.m N:=by
    change X.vesselsC.y X.m+(X.vesselsC.draws.S.scale (X.m+X.i)-X.vesselsC.draws.S.scale X.m)+(X.i:ℝ)=_
    rw [same,←finish]
    unfold Compar
    simp only [Nat.add_sub_cancel_left]
  refine ⟨X.windowC.warm,site ▸ (window R s X.m N live start fine).2.2.1⟩

end YM.Integration.WilsonIndependentMovingRosterMarginLedger

