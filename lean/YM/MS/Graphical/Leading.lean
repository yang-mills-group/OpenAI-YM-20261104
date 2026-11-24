import YM.MS.Graphical.Enumeration
import YM.MS.Mach.Land
/-! Bulk and marked vertices of the fixed continuum graph formula. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical.Diagram
open Arts Pearl Local.Physical Land Motif.Literal

variable {G : Gauge}
def bulk (G : Gauge) (n : ℕ) := allPages 4 (0:ℕ→ Mob G) (ambient n) true
def sectorMark (G : Gauge) (h : ℕ) (a : ℕ → Mob G) (n : ℕ) : Flats G := allPages h a (insertions h n) false
def sectorSeed {D : Deck G} (A : Booked D) (h : ℕ) (v : Plaid D h) : ℕ → Mob G :=
  linear (Mob G) (A.optics h v)

end YM.MS.Graphical.Diagram
