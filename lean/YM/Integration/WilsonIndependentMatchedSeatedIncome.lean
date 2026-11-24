import YM.Integration.WilsonIndependentMatchedCoverMixed
import YM.Integration.WilsonIndependentMatchedCoverHome
import YM.Integration.WilsonIndependentMatchedVacant
import YM.Integration.WilsonIndependentMatchedCoverSum

/-! Native seated income including the installed source's value on its own
report. A compensated cut supplies it from the issued bound on its entire
rooted word, before any positional summation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedSeatedIncome
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedCoveredSeats
variable {G:Gauge}{e:ℕ}{E:Credit}
structure Funds {D:ℕ}(R:Realm G (e+1) E)(l d m n u b:ℕ)(φ:Rarity D)(y:ℝ)(o:CellR)
    (δ α A B:ℝ)(P:ℕ → Era G ℝ):Prop where
  head:∀ i ≤ n,Auth l (P i)
  cash:∀ i<n,let x:=paceT R.draws.S m (m+(i+1))
    Income (P (i+1)) l e (u+b) (OrbP (ll R.draws (m+i)) φ x y o)
      (charge φ (u+b) d x y (A*(δ/x)^α) B)
  empty:∀ i<n,¬(VisitsT φ (paceT R.draws.S m (m+(i+1))) y o).Nonempty → P (i+1)=0
  home:Flush e u 1 (P 0) (WilsonIndependentMatchedCoverHome.bill φ u d y (A*δ^α) B)

variable {h D k v₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k v₀ e}{W K U:Credit}

theorem stable (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR)
    (δ A B:ℝ)(test:Amplitude φ B)(u b:ℕ)(moment:u+b ≤ v₀)
    (paid:∀ i ≤ X.i,∀ j ≤ e,∀ r:ℕ,∀ t ≤ v₀,Fruit 0 1 t ((a • X.springP i).2 j r)
      (A*(δ/paceT X.ax.S X.m (X.m+i))^(1/4:ℝ))):
    Funds X.vesselsC k h X.m X.i u b φ y o δ (1/4) A B (seat X a φ y o):=by
  refine ⟨(traced X a φ y o).1,?_,?_,?_⟩
  · intro i hi
    exact submitted _ ((X.onward hi).μ a) _ (fun j hj r=>paid _ hi j hj r _ moment)
      φ _ y o h _ (pace_pos ..) (pace_le _ (Nat.le_add_right _ _)) test
  · intro i hi none
    exact WilsonIndependentMatchedVacant.absent _ φ _ y o h (pace_pos ..) none
  · have atHome (j:ℕ)(hj:j ≤ e)(r:ℕ):Fruit 0 1 u ((a • X.springP 0).2 j r)
        (A*δ^(1/4:ℝ)):=by
      simpa only [Nat.add_zero,pace_self,div_one] using paid 0 (Nat.zero_le _) j hj r u
        ((Nat.le_add_right u b).trans moment)
    simpa only [WilsonIndependentMatchedCoveredSeats.seat,Nat.add_zero,pace_self] using
      (WilsonIndependentMatchedCoverHome.placed _ ((X.onward (Nat.zero_le _)).μ a)
        φ y o h _ B test atHome).f_l

end YM.Integration.WilsonIndependentMatchedSeatedIncome
