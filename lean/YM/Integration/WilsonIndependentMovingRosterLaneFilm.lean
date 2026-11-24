import YM.Integration.WilsonIndependentMovingRosterLaneEdge
import YM.Integration.WilsonIndependentMovingRosterLaneSalary

/-! The complete fitted field and its signed stable companion at one
filed destination. A fitted peer can also be submitted a direction at a
time, before the external coefficients are multiplied back in. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterLaneFilm
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterSlots (degree count wallet entry)
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMovingRosterLaneEdge (OnEdge)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}

/-- `c=dose X a` gives the full fitted operand. Other genuine doses may
be used on the same cut and paid at their own unscaled price. -/
def Licensed (X:CutsP H T p v E W K U)(R:Realm G (e+1) E)(home N:ℕ)(a δ A:ℝ):Prop:=
  ∀(flag:Bool)(c:Verse F)(φ:Rarity D)(y z:ℝ)(o:CellR)(B:ℝ),Amplitude φ B → radiusH φ 1 y ≤ z →
    ∀u b:ℕ,u+b ≤ u₀ →
      let P:=entry flag X a c φ y o
      let amt:=wallet flag X c A u b
      0 ≤ amt ∧ Lane R (degree flag k h) h home (N-home) N u b φ y o δ ((count flag:ℝ)/4) amt B P ∧
        ∀j:ℕ,home ≤ j → j < N → OnEdge R (degree flag k h) u b home N j φ y o P
          (offer u b h (count flag) z δ (paceT R.draws.S home (j+1)) amt B)

theorem from_bought (X:CutsP H T p v E W K U)(a δ A:ℝ)(top:X.N=X.ceilC)(mesh:0 < δ)(price:0 ≤ A)
    (paid:WilsonIndependentMatchedCoverPairBudget.Bought X a δ A):
    Licensed X X.vesselsC X.m X.N a δ A:=by
  have countEq:X.i=X.N-X.m:=by change X.N=X.m+X.i at top;omega
  intro flag c φ y z o B test house u b room P amt
  have wage:=WilsonIndependentMatchedRosterSlots.money flag X c price u b
  have landed:=WilsonIndependentMatchedRosterSlots.source flag X a c φ y o δ A B paid test u b room
  rw [countEq] at landed
  exact ⟨wage,landed,fun j below fine=>WilsonIndependentMovingRosterLaneEdge.original X.vesselsC (degree flag k h)
    h (count flag) X.m X.N j u b below fine φ y z o δ amt B P mesh wage test house landed⟩

/-- All cuts use one previously issued moisture tariff. The fitted
salary is still the cost of the actual complete report at that cut. -/
theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u₀ e)(E W K U:Credit):
    ∃C:Credit,∀X:CutsP H T p v E W K U,X.N=X.ceilC → ∀a fee:ℝ,0 < a → X.fuel=a*fee →
      Licensed X X.vesselsC X.m X.N a⁻¹ (paceT X.ax.S X.m X.N) (C.buy X.Age*fee):=by
  obtain ⟨C,price⟩:=WilsonIndependentMovingRosterLaneSalary.original H T p v E W K U
  refine ⟨C,?_⟩
  intro X top a fee ha fuel
  have hf:=X.hf
  rw [fuel] at hf
  exact from_bought X _ _ _ top (pace_pos ..)
    (mul_nonneg (zero_le_one.trans (C.purchase X.windowC.warm)) ((mul_nonneg_iff_of_pos_left ha).1 hf))
    (price X top a fee ha fuel)

end YM.Integration.WilsonIndependentMovingRosterLaneFilm

