import YM.Integration.WilsonMatrixTicketLanesTwoSites
import YM.Integration.WilsonInvariantActionOnePoint
import YM.RG05Readout.Bay.Needle

/-! The elected two-site Maxwell detector actually sees the scalar Ward action.
One spectator works at a fixed separation and under every sufficiently narrow
original smooth packet around those same two points. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPairProbe
open Filter Set Function Table Spec Climb Maxwell Maxwell.Free RG05Readout Trace.Pilot
open WilsonMatrixTicketLanesTwoSites
open scoped Classical Topology
variable {G : Gauge} (C : Family G)
local notation "B" => Bel C.book

def place : Points 2 := pairPoints 0 (basis timeAxis)

def reading (w : (standard C.labels).Ref 4) (z : Points 2) : ℂ :=
  (Bel C.book).read z (Fin.cons ⟨4,(Bel C.book).representative 4 (stepField C)⟩ (fun _=>⟨4,w⟩))

theorem at_place (w : (standard C.labels).Ref 4) :
    reading C w place=(Bel C.book).spectra 4 (stepField C) (shell C.labels 4 w) := by
  change (Bel C.book).replies 4 ((Bel C.book).representative 4 (stepField C)) (shell C.labels 4 w)=_
  rw [← (Bel C.book).projected,(Bel C.book).rep]

/-- A common spectator from the submitted finite decoder. No tangent basis
identification of the action is assumed. -/
theorem selected (simple : G.Simple) (H : (Bel C.book).Hierarchy) (D : Contacts.Foci B 4)
    (sites : ∀j:D.index,∃w:(standard C.labels).Ref 4,D.shell j=shell C.labels 4 w) :
    ∃ (j:D.index) (w:(standard C.labels).Ref 4),
      D.shell j=shell C.labels 4 w ∧ reading C w place≠0 ∧
      ∀ᶠm:ℕ in atTop,∃fit:Bay.sand place (C.S.a m/16)⊆conf 2,
        ‖reading C w place‖/2 ≤ ‖(Bay.Packet (C:=C) place m fit).applyTo (reading C w)‖ := by
  have occupied : ∃j:D.index,(Bel C.book).spectra 4 (stepField C) (D.shell j)≠0 := by
    by_contra! vanish
    apply scale_alive simple H
    change stepField C=0
    rw [←D.detects (stepField C),show (fun j=>(Bel C.book).spectra 4 (stepField C) (D.shell j))=0 from funext vanish,map_zero]
  obtain ⟨j,hj⟩:=occupied
  obtain ⟨w,hw⟩:=sites j
  have hn : reading C w place≠0:=by simpa only [at_place,hw] using hj
  refine ⟨j,w,hw,hn,?_⟩
  have sep : place∈conf 2:=(shell C.labels 4 w).clear
  have sc : ContinuousOn (reading C w) (conf 2):=((Bel C.book).smooth_read H.smooth _).continuousOn
  have pos : 0<‖reading C w place‖/2:=half_pos (norm_pos_iff.mpr hn)
  filter_upwards [Bay.converging (C:=C) place sep (fun _=>place) tendsto_const_nhds
    (reading C w) sc _ pos] with m hm
  obtain ⟨fit,bound⟩:=hm
  refine ⟨fit,?_⟩
  have gap:=norm_sub_norm_le (reading C w place) ((Bay.Packet (C:=C) place m fit).applyTo (reading C w))
  rw [norm_sub_rev] at gap
  linarith

theorem original (simple : G.Simple) (H : (Bel C.book).Hierarchy) :
    ∃ D : Contacts.Foci B 4,∃ (j:D.index) (w:(standard C.labels).Ref 4),
      D.shell j=shell C.labels 4 w ∧ reading C w place≠0 ∧
      ∀ᶠm:ℕ in atTop,∃fit:Bay.sand place (C.S.a m/16)⊆conf 2,
        ‖reading C w place‖/2 ≤ ‖(Bay.Packet (C:=C) place m fit).applyTo (reading C w)‖ := by
  obtain ⟨D,sites⟩:=WilsonMatrixTicketLanesTwoSites.fixed C.labels 4
  exact ⟨D,selected C simple H D sites⟩

end YM.Integration.WilsonInvariantActionPairProbe
