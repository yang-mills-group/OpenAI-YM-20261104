import YM.Integration.WilsonThermometerOriginalPanelDates
import YM.Integration.WilsonPositionProgramPublicStations

/-! The signed two-point tests and the public invoice at a nominated
sequence of original quick-panel dates. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterPanelCourse
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d:ℕ}{W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}
    {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (B:Binding C)(H:C.Makes)(O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
variable {F:Extraction.Order}{S:Table C.book}(U:Final C F S)(a:(Cells.standard C).Hierarchy)
variable (simple:G.Simple)(fund:Scrim C W u ψ φ δ (fly C.path.levels) r L)
    {z:ℝ}(earns:∀i≤d,generator G i≤z)

include H simple fund earns
theorem pairs (P:ℕ→ Fin 3→ Tapes.Panel d)(fees:ArcSky P)
    (k:ℕ→ℕ)(late:Tendsto k atTop atTop)(Y:ℕ→ℕ→ℕ→TableL C d)
    (bought:∀i,PoisedSky (P (k i)) B H O J (MergeProof.East.trays d) z (k i) (Y i))
    (ε:ℝ)(pos:0<ε):∀ᶠ i in atTop,SeqPair (k i) (P (k i) 0).arc d (Y i) ε:=by
  let t(w:Fin (d+1)):=fun _:Fin 2=>w
  have pair(w:Fin (d+1))(p:Fin 2→PegC C w):=late.eventually
    (lava_vSky P fees B H simple fund O J z earns (t:=t w)
      (fun v=>ladder C w (PoleC C w (p v))) 0 (window_closed (100:ℝ) 2)
      (fun x hx=>spaced_conf (by norm_num) hx.1) (n:=MergeProof.East.trays d) (Nat.le_add_left ..) (Nat.le_add_left ..))
  filter_upwards [eventually_all.mpr (fun w=>eventually_all.mpr (pair w)),
    late.eventually (open_readSky simple 100 A 2),
    ((Ship.diminishes A (MergeProof.East.trays d) simple (by unfold MergeProof.East.trays;omega)).comp late).eventually (ge_mem_nhds pos)] with i bound fit price
  constructor
  · obtain ⟨q,v,order,_⟩:=(bought i).supply 0
    exact fit _ (by rw [← (P (k i) 0).factor (C.path.levels.clock.J (k i))];exact order.age.allot.permitted)
  · intro w p N l hn y v x seen fits name occupied
    exact (bound w p (Y i) (bought i) N l hn x seen fits name occupied).trans price

include U in
theorem registered (P:ℕ→ Fin 3→ Tapes.Panel d)(fees:ArcSky P)
    (b:Fin 3→ℝ)(offset:ℕ→ℝ)(range:∀i,offset i∈Icc 0 1)
    (arc:∀i j,(P i j).arc=b j+offset i)(κ:ℝ)(checks:Checks (b 0) (b 1) (b 2) κ (MergeProof.East.trays d) d)
    (base:5<b 0)(k:ℕ→ℕ)(late:Tendsto k atTop atTop)
    (Y:ℕ→ℕ→ℕ→TableL C d)
    (bought:∀i,PoisedSky (P (k i)) B H O J (MergeProof.East.trays d) z (k i) (Y i)):
    ∀ᶠ i in atTop,TimberSky F a d (k i) d (b 0+offset (k i)) κ (Y i):=by
  have pair:=pairs B H O J simple fund earns P fees k late Y bought (costHint d) (cost_pos _)
  have gran:=podiumSky P fees B H simple fund O J z earns F (Nat.le_add_left ..)
    (sizeHint d) (by unfold sizeHint;positivity) a.smooth a.spin b offset
    (fun i=>(range i).1) arc checks k late Y bought
  have invoice:=supply_wheel _ gran U.room.ordered U.room.kernel.smooth H U.room.generic
    a.smooth (show 0<sizeHint d by unfold sizeHint;positivity) (costHint d) (cost_pos _)
  filter_upwards [invoice,pair,((Perch.y_rate.comp ((hat_rate A simple).comp late)).eventually_ge_atTop (b 0+1)),
    late.eventually (eventually_all.mpr (fun v:Fin (d+1)=>eventually_ge_atTop (C.ref v)))] with i bill price wide floor
  rw [←arc]
  refine ⟨⟨?_,?_⟩,floor,fun N p valid=>⟨(bought i).charts _ _ valid,(bought i).bank _ _ valid⟩,price,?_⟩
  · rw [arc];exact base.trans_le (le_add_of_nonneg_right (range _).1)
  · rw [arc];exact (add_le_add_right (range _).2 _).trans wide
  · refine {lift_bound:=bill.lift_bound,lift_unit:=bill.lift_unit,lift_signed:=bill.lift_signed,
            lift_real:=bill.lift_real,short:=fun {n} hn=>bill.short (le_trans hn (Nat.le_add_right ..))}

end YM.Integration.WilsonMovingForkReporterPanelCourse
end
