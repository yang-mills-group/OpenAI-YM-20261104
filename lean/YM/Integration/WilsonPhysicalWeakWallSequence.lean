import YM.Integration.WilsonPhysicalWeakWallStaff

/-! One choice of weak orientation and reflected wall for all finite requests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakWallSequence
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open scoped Topology ContDiff Classical BigOperators

open WilsonPositionThermometerOrientedStation WilsonPositionThermometerCapStation
open WilsonPhysicalWeakWheelOffers
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {Y : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch C}
    (h : G.Simple) (F : Final C f S) (H : (Bel C.book).Hierarchy)
    (hZ : Bliss F Y arch H) {c : ℕ} {I : Type} [Fintype I]
    (d : I → Fin (c+1)) (u : ∀ i, (Bel C.book).Field (d i))

open WilsonPhysicalWeakWallStaff
include hZ in
theorem original:∃W:ℝ→Seats C S c,∀m:ℕ,∀ᶠr in trail,Booked (Y:=Y) h F H d u (W r) r m:=by
  let B(r:ℝ)(m:ℕ):Set (Seats C S c):={w|Booked (Y:=Y) h F H d u w r m}
  have supplied(m:ℕ):∀ᶠr in trail,(B r m).Nonempty:=
    WilsonPhysicalWeakWallStaff.original h F H hZ d u m
  let M (r : ℝ) := (Finset.range (glen C.S r+1)).filter fun m => (B r m).Nonempty
  have available (r : ℝ) {m} (hm : m ∈ M r) : (B r m).Nonempty := (Finset.mem_filter.mp hm).2
  obtain ⟨r₀,defaultPair,_⟩ := (supplied 0).exists
  let W (r : ℝ) := if h : (M r).Nonempty then (available r (Finset.max'_mem (M r) h)).choose else defaultPair
  refine ⟨W,fun m => ?_⟩
  filter_upwards [supplied m,(glen_leads C.S).eventually_ge_atTop m] with r hr hg
  have hm : m ∈ M r := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hg),hr⟩
  have live : (M r).Nonempty := ⟨m,hm⟩
  dsimp only [W]
  rw [dif_pos live]
  obtain ⟨prices,axes,earned⟩:=(available r (Finset.max'_mem (M r) live)).choose_spec
  exact ⟨prices,axes,fun j hj=>earned j (hj.trans (Finset.le_max' _ _ hm))⟩

end YM.Integration.WilsonPhysicalWeakWallSequence
