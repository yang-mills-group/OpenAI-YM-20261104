import YM.SignedWilsonExpansion.Homes.Meaty
import YM.SignedWilsonExpansion.Homes.SetsA

/-! A single physical staff for all growing finite caps and their signed weak basis vectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakWallStaff.ReStaff
open Function Set Filter Finset Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open WilsonPositionThermometerOrientedStation WilsonPositionThermometerCapStation
open WilsonPhysicalWeakWallStaff
open scoped Topology Classical BigOperators
open PhysicalNext.Repeat.Legato SignedWilsonExpansion.Homes Integration.WilsonLimitConstruction
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{Y:Ultrafilter (ℕ×ℕ)}
variable (sg:G.Simple)(F:Final R.family f S)(H:(Bel R.family.book).Hierarchy){arch:Trace.Terrace.Arch R.family}(bliss:Bliss F Y arch H)

abbrev slot {G:Gauge}(C:Family G)(D:ℕ):Type:=
  Σj:Fin (D+1),Fin (Module.finrank ℂ ((Bel C.book).Field j))
def head {G:Gauge}(C:Family G){D:ℕ}(i:slot C D):(Bel C.book).Field i.1:=
  Module.finBasis ℂ _ i.2
abbrev Day (C:Family G)(S:Table C.book):=ΣD:ℕ,Seats C S D
local notation "C"=> R.family
def breadth (B:Day R.family S):BeamT R.family:= ⟨B.2.room.horizon,B.2.room.station⟩
def Roomy (B:Day R.family S)(r:ℝ):Prop:= B.2.room.station.checked (track f) H B.2.room.horizon ∧ Booked (Y:=Y) sg F H (fun i:slot C B.1=>i.1) (head C) B.2 r B.1
include bliss in
theorem mile (trackP:(track f).Ordered R.family S) (hT:FullVolume.PositionsUV R.family Extraction.Sequence.full)
    (budget:R2I.RG05Joint.AcrossPanels R.kit):∃day:ℝ→Day C S,Tendsto (fun r=>(day r).1) trail atTop ∧
    ∀ᶠr in trail,Roomy (Y:=Y) sg F H (day r) r:=by
  let A(r:ℝ)(m:ℕ):Set (Seats C S m):={w|Roomy (Y:=Y) sg F H ⟨m,w⟩ r}
  have paid(m:ℕ):∀ᶠr in trail,(A r m).Nonempty:=
    WilsonPhysicalWeakWallStaff.windowsPV R sg F H bliss (fun i:slot C m=>i.1) (head C) m trackP hT budget
  let M(r:ℝ):=(range (glen (C).S r+1)).filter fun m=>(A r m).Nonempty
  have get(r:ℝ){m:ℕ}(hm:m∈M r):(A r m).Nonempty:=(mem_filter.mp hm).2
  obtain ⟨r₀,w₀,_⟩:=(paid 0).exists
  let day(r:ℝ):Day C S:=if h:(M r).Nonempty then
    ⟨(M r).max' h,(get r (max'_mem (M r) h)).choose⟩ else ⟨0,w₀⟩
  have issues(m:ℕ):∀ᶠr in trail,m≤(day r).1 ∧ Roomy (Y:=Y) sg F H (day r) r:=by
    filter_upwards [paid m,(glen_leads (C).S).eventually_ge_atTop m] with r room size
    have hm:m∈M r:=mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le size),room⟩
    have live:(M r).Nonempty:=⟨m,hm⟩
    dsimp only [day]
    rw [dif_pos live]
    exact ⟨le_max' _ _ hm,(get r (max'_mem (M r) live)).choose_spec⟩
  exact ⟨day,tendsto_atTop.mpr fun m=>(issues m).mono fun _ h=>h.1,(issues 0).mono fun _ h=>h.2⟩

private lemma axes (P:ℝ→tower S)(hP:∀ j:ℕ,∀ᶠ r in trail, Staff (Y:=Y) sg F H r (P r) j)(d:ℕ):∀ᶠ r in trail, obedient F H (P r) d:= (hP d).mono fun _ hi=>hi.spins (Fin.last d)
private lemma leading (P:ℝ→tower S)(hP:∀ j:ℕ,∀ᶠ r in trail, Staff (Y:=Y) sg F H r (P r) j) : Leading F P where
    equivariant d := (axes sg F H P hP d).mono fun i hi=>obedient_realH F sg H hi
    raised := fun {d e} h=>(hP e).mono fun i hi=> hi.rises (Fin.last e) ⟨d,Nat.lt_succ_of_le h⟩
    unit d := (axes sg F H P hP d).mono fun i hi=> hi.unit
    lead n d v j L hl h := by
      refine measured_tensor F (r:=fun r:ℝ=>r) (v:=fun _=>none) (w:=fun _=>v) (l:=trail) self_mem_nhdsWithin d j (fun i=> PoleC C (d i)) hl h ?_ (fun _=>tendsto_const_nhds)
      intro p; rw [Metric.tendstoUniformlyOn_iff]; intro ε he
      obtain ⟨i,hi,ht,h₁,h₂,h₃⟩:= ((eventually_ge_atTop j).and ((eventually_ge_atTop n).and ((eventually_all.mpr (fun i=> eventually_ge_atTop (d i))).and ((size_ascends.eventually (Work.A05.compact_fits hl h)).and (cost_clears.eventually (gt_mem_nhds he)))))).exists
      let n':Fin (i+1):= ⟨n,Nat.lt_succ_of_le ht⟩; let d':Fin n'→ Fin (i+1):= fun x=>⟨d x,Nat.lt_succ_of_le (h₁ x)⟩
      filter_upwards [hP i] with r hp x hx; rw [dist_comm,dist_eq_norm]; exact (hp.checks n' d' p ⟨j,Nat.lt_succ_of_le hi⟩ x (h₂ hx)).trans_lt h₃

def preframe (day:ℝ→Day C S)(r:ℝ):tower S:=(day r).2.frame
variable (day:ℝ→Day R.family S) (rises:Tendsto (fun r=>(day r).1) trail atTop)
    (sold:∀ᶠr in trail,Roomy (Y:=Y) sg F H (day r) r)
include rises sold
lemma masterPV : ( ∀d, ∀ᶠr in trail, PhysMS.Frame.obedient F H (preframe day r) d ) ∧ Leading F (preframe day):= by
  have h(m:ℕ):∀ᶠ r in trail,Staff (Y:=Y) sg F H r (preframe day r) m:=by
    filter_upwards [sold,rises.eventually_ge_atTop m] with i hi hh
    exact (hi.2.2.2 _ hh).1
  exact ⟨axes sg F H _ h,leading sg F H _ h⟩
lemma ticketPV : Tendsto (fun r=>(breadth (day r)).k) trail atTop ∧ ∀ᶠ r in trail, (breadth (day r)).Given (track f) H r := by
   refine ⟨tendsto_atTop.2 (fun m=>?_), sold.mono (fun r hi=> ?_)⟩
   · exact (rises.eventually_ge_atTop m).mono fun i hi=> hi.trans (day i).2.room.fits
   exact ⟨hi.1, (hi.2.2.2 (day r).1 le_rfl).2.2.2.1⟩

end YM.Integration.WilsonPhysicalWeakWallStaff.ReStaff
