import YM.Integration.WilsonPositionThermometerStationReading

/-! The missing legs in the finite thermometer use the physical unit on the
same oriented station. The resulting faces are literal subproducts of three
fixed cutoff observables, with all its signed finite moments on one law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerStationUnit
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open Ward Climb Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato XSpace XSpace.Rose
open Trace Trace.Pilot MergeProof.East
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {H : (Bel C.book).Hierarchy}
    {d : ℕ} (V : Vane C d) (j : Fin (d+1))
variable (cal : C.Makes) (checked : V.checked f H d)

include cal checked in
theorem original : ∀ᶠ z : UVIndex in f.fuse,
    V.wheel.atCut z j ((Bel C.book).unit j) = C.book.scalar j ∧
    ∀ x : Site (C.side z.1 z.2), C.O z.1 z.2 (V.wheel.atCut z j ((Bel C.book).unit j)) x = 1 := by
  filter_upwards [large_mesh f (V.k+1),large_mesh f (C.ref j)] with z late ref
  have eq : V.wheel.atCut z j ((Bel C.book).unit j) = C.book.scalar j := by
    change Next.Rank.East.ladd C _ _ _ _ _ _ (Further.CorrectedLift.ladder C j ((Bel C.book).unit j))=_
    rw [Further.CorrectedLift.ladder_unit]
    exact Next.Rank.East.pure_start cal (checked.early j) (Nat.le_of_lt late) _ _ ((checked.rate _ _ late).1 j).1
  exact ⟨eq,fun x => eq ▸ C.constant cal _ ref x⟩

variable (v : Fin 3 → (Bel C.book).Field j)

def slot (s : Badge) (i : Fin 3) : (Bel C.book).Field j := if i ∈ s then v i else (Bel C.book).unit j

def face (z : UVIndex) (x : Fin 3 → Site (C.side z.1 z.2)) (s : Badge) : ℂ :=
  C.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin 3 => j) x (fun i => V.wheel.atCut z j (slot j v s i))

include cal checked in
theorem subproducts : ∀ᶠ z : UVIndex in f.fuse, ∀ (x : Fin 3 → Site (C.side z.1 z.2)) (s : Badge),
    face V j v z x s = ∫ U, ∏ i ∈ s, C.O z.1 z.2 (V.wheel.atCut z j (v i)) (x i) U ∂law G _ (C.beta z.1 z.2) := by
  filter_upwards [original V j cal checked] with z paid x s
  change (∫ U, ∏ i, C.O z.1 z.2 (V.wheel.atCut z j (slot j v s i)) (x i) U ∂_) = _
  congr 1
  funext U
  have per (i : Fin 3) : C.O z.1 z.2 (V.wheel.atCut z j (slot j v s i)) (x i) U =
      (if i ∈ s then C.O z.1 z.2 (V.wheel.atCut z j (v i)) (x i) U else 1) := by
    by_cases hi : i ∈ s
    · simp [slot, hi]
    · simp only [slot,if_neg hi]
      exact congrFun (paid.2 (x i)) U
  simp_rw [per]
  simp

end YM.Integration.WilsonPositionThermometerStationUnit
end
