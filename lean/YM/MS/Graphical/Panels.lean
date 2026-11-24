import YM.MS.Graphical.ManyRoot
import YM.MS.Graphical.Leading
import YM.MS.Puff.State
import YM.MS.Graphical.PricePin
import YM.MS.Rake.Sequence

/-! Finite parts, infrared limit and assembly of the renormalized graph sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Filter Land Local.Physical Pearl Rake

variable {I : Type} [LinearOrder I] {G : Gauge} {B : Deck G}

def bulkSchedule (G : Gauge) (y : ℝ) (k : ℕ) : Schedule G := fun t=> Parade (Diagram.bulk G k) 4 y t

variable (X : Booked B) (u : I → Label B) (y : ℝ)

def markerPage (X : Booked B) (u : Label B) :=
  Diagram.sectorMark G u.h (Diagram.sectorSeed X u.h u.item)

def singleSchedule (X : Booked B) (u : Label B) (y : ℝ) (k : ℕ) : Schedule G := fun t=>
   Parade (markerPage X u k) u.h y t

def allScale (x : I → Tone.QP) : Population G I := ⟨fun i=>(u i).h, x,y,bulkSchedule G y,fun i=>singleSchedule X (u i) y⟩

def irRemoved (x : I→Tone.QP) (s : Finset I) (k : ℕ): ℂ := limUnder atTop (fun t:ℝ=> regularPart (Population.clusters (allScale X u y x) s k) t 0 [])

def fullGraph (x : I→Tone.QP) := Puff.Mom.bouquet (irRemoved X u y x)

end YM.MS.Graphical
