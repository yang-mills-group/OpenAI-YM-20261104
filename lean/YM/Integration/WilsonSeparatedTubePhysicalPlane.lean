import YM.Integration.WilsonSeparatedTubeCoordinates

/-! Exact evaluation of the true unselected hierarchy on its ordered physical plane.
Both the grades and the local fields are arbitrary finite data. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedTubePhysicalPlane
open Set Extraction Table Spec Boundary Boundary.Surface GapsContact GapsContact.Ascent GapsContact.Tunnel EveryPhase
open WilsonSeparatedTubeCoordinates
open scoped Topology Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (L : Almanac F) {n : ℕ}

theorem ordered (D : ∀ k, Blanket k) (X : (Survey.reads L none).world.Aurora D)
    {d : Fin n → ℕ} (v : ∀ i,S.Field (d i)) (x : SpacePoints n) (y : Heights n) (hy : y∈east n) :
    X.emit (fun i=>S.pin (d i) (v i)) (plane x y) = S.classMoment S d (place x y) v := by
  let fields (i : Fin n) : S.Tag := ⟨d i,v i⟩
  have clean : trace (place x (0 : Heights n)) = x := by funext j; simp [trace,place]
  have clocks : shift (place x (0 : Heights n)) y = fun j=>(y j:ℂ)*Complex.I := by
    funext j; simp [shift,place]
  have ht := (observe L (none : Survey F) X).2.pure n (fun i=>S.pin (d i) (v i))
    (place x (0 : Heights n)) y hy
  change X.emit _ (plane x y) = F.B.waves.F n _ _ _ at ht
  rw [clocks,clean] at ht
  exact ht.trans (F.realization.allWorld.heat.roots n fields x y hy)

theorem read (D : ∀ k, Blanket k) (X : (Survey.reads L none).world.Aurora D)
    {d : Fin n → ℕ} (v : ∀ i,S.Field (d i)) {r : ℝ} (hr : 0<r)
    (x : SpacePoints n) (y : Heights n) (hy : y∈east n) :
    weather X (fun i=>S.pin (d i) (v i)) r (plane x y) = S.classMoment S d (r • place x y) v := by
  have hh : r • y∈east n := fun i j h=>mul_lt_mul_of_pos_left (hy h) hr
  simpa only [weather,plane_mul,place_mul] using ordered F L D X v (r • x) (r • y) hh

end YM.Integration.WilsonSeparatedTubePhysicalPlane
