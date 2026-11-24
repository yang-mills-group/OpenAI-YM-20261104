import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Land

/-! Identification of independently prepared pole tables after checking their
actual recursion and the opted-in bare marked input. -/

set_option autoImplicit false
noncomputable section

namespace YM.MS.Land

open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Rock Path Oceans
open Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting Local.Physical
open Mach Train Pearl Emit Wind Wind.Leading Menus Program Knobs

theorem original_external_bulk_germ {G : Gauge} {D : Deck G} {A : Booked D}
    (T : MS_Data G A) {X : Blue G} {p : CostsM G}
    (prepared : leader G X (gloss (pulseX G)) p) :
    p = T.poleS ∧ ∀ i, Pact (X i) (T.bulk i) :=
  Dock.unique_B prepared T.bulkOK

theorem original_external_marked_germ {G : Gauge} {D : Deck G} {A : Booked D}
    (T : MS_Data G A) {X Y : Blue G} {p q : CostsM G}
    (bulk : leader G X (gloss (pulseX G)) p) (d : ℕ) (v : Plaid D d)
    (marked : comet d 0 X (gloss (Literal.linear (Mob G) (A.optics d v))) Y q) :
    q = T.poles d v ∧ ∀ i, Pact (Y i) (T.marks d v i) :=
  Dock.unique_M marked (T.markOK d v) (original_external_bulk_germ T bulk).2

end YM.MS.Land
