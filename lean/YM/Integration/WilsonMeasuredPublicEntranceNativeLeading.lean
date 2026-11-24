import YM.Integration.WilsonMeasuredPublicEntranceNativeStaff

/-! The position tower and its common home coordinates are purchased before the neighboring radius. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLeading
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open scoped Topology ContDiff Classical BigOperators

open WilsonPositionThermometerOrientedStation WilsonPositionThermometerCapStation
open WilsonPhysicalWeakWheelOffers
open WilsonPhysicalWeakWallBounded (atBasis slot head cost)
open Trace.Terrace Trace.Over FVA2 FVA2.Register
open WilsonMeasuredPublicEntranceNativeStaff
open private leading from YM.Integration.WilsonPhysicalWeakSundial
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
  {Y:Ultrafilter (ℕ×ℕ)} (h:G.Simple)(F:Final C f S)(H:(Bel C.book).Hierarchy)
  (U:ℝ→tower S)

def Offered (r:ℝ)(m:ℕ):Prop:=
  ∃A:tower S,∀ j ≤ m,Receipt (Y:=Y) h F H r (U r) A j

theorem original (sold:∀m,∀ᶠr in trail,Offered (Y:=Y) h F H U r m):
    ∃J:ℝ→tower S,Leading F J ∧ localCost trail U J ∧
      ∀m,∀ᶠr in trail,Receipt (Y:=Y) h F H r (U r) (J r) m:=by
  classical
  let M(r:ℝ):=(Finset.range (glen C.S r+1)).filter fun m=>Offered (Y:=Y) h F H U r m
  have get(r:ℝ){m:ℕ}(hm:m∈M r):Offered (Y:=Y) h F H U r m:=(Finset.mem_filter.mp hm).2
  let J(r:ℝ):tower S:=if hm:(M r).Nonempty then (get r (Finset.max'_mem (M r) hm)).choose else U r
  have bought (m:ℕ):∀ᶠr in trail,Receipt (Y:=Y) h F H r (U r) (J r) m:=by
    filter_upwards [sold m,(glen_leads C.S).eventually_ge_atTop m] with r sale size
    have hm:m∈M r:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le size),sale⟩
    have live:(M r).Nonempty:=⟨m,hm⟩
    dsimp only [J]
    rw [dif_pos live]
    exact (get r (Finset.max'_mem (M r) live)).choose_spec m (Finset.le_max' _ _ hm)
  refine ⟨J,leading h F H J (fun m=>(bought m).mono fun _ s=>s.1),?_,bought⟩
  intro d v
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  have fee:Tendsto (fun m=>cost C v * costHint m) atTop (𝓝 0):=by
    simpa only [mul_zero] using cost_clears.const_mul (cost C v)
  obtain ⟨m,room,small⟩:=((eventually_ge_atTop d).and (fee.eventually_lt_const ep)).exists
  filter_upwards [bought m] with r read
  exact (dist_eq_norm ..).trans_lt ((read.2 d room v).trans_lt small)

end YM.Integration.WilsonMeasuredPublicEntranceNativeLeading
end
