import YM.Integration.WilsonPhysicalWeakWallBounded

/-! A single physical staff for all growing finite caps and their signed weak basis vectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakRisingStaff
open Function Set Filter Finset Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open WilsonPositionThermometerOrientedStation WilsonPositionThermometerCapStation
open WilsonPhysicalWeakWallStaff WilsonPhysicalWeakWallBounded
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{Y:Ultrafilter (ℕ×ℕ)}
variable (sg:G.Simple)(F:Final C f S)(H:(Bel C.book).Hierarchy){arch:Trace.Terrace.Arch C}(bliss:Bliss F Y arch H)

abbrev Day (C:Family G)(S:Table C.book):=ΣD:ℕ,Seats C S D

def Served (a:Day C S)(r:ℝ):Prop:=Booked (Y:=Y) sg F H (fun i:slot C a.1=>i.1) (head C) a.2 r a.1

include bliss in
theorem original:∃day:ℝ→Day C S,Tendsto (fun r=>(day r).1) trail atTop ∧
    ∀ᶠr in trail,Served (Y:=Y) sg F H (day r) r:=by
  let A(r:ℝ)(m:ℕ):Set (Seats C S m):={w|Served (Y:=Y) sg F H ⟨m,w⟩ r}
  have paid(m:ℕ):∀ᶠr in trail,(A r m).Nonempty:=
    WilsonPhysicalWeakWallStaff.original sg F H bliss (fun i:slot C m=>i.1) (head C) m
  let M(r:ℝ):=(range (glen C.S r+1)).filter fun m=>(A r m).Nonempty
  have get(r:ℝ){m:ℕ}(hm:m∈M r):(A r m).Nonempty:=(mem_filter.mp hm).2
  obtain ⟨r₀,w₀,_⟩:=(paid 0).exists
  let day(r:ℝ):Day C S:=if h:(M r).Nonempty then
    ⟨(M r).max' h,(get r (max'_mem (M r) h)).choose⟩ else ⟨0,w₀⟩
  have issues(m:ℕ):∀ᶠr in trail,m≤(day r).1 ∧ Served (Y:=Y) sg F H (day r) r:=by
    filter_upwards [paid m,(glen_leads C.S).eventually_ge_atTop m] with r room size
    have hm:m∈M r:=mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le size),room⟩
    have live:(M r).Nonempty:=⟨m,hm⟩
    dsimp only [day]
    rw [dif_pos live]
    exact ⟨le_max' _ _ hm,(get r (max'_mem (M r) live)).choose_spec⟩
  exact ⟨day,tendsto_atTop.mpr fun m=>(issues m).mono fun _ h=>h.1,(issues 0).mono fun _ h=>h.2⟩

end YM.Integration.WilsonPhysicalWeakRisingStaff
