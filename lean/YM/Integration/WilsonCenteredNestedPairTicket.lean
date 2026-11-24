import YM.Integration.WilsonCenteredNestedPairConvoy

/-! Use the genuine signed raw tree ticket at the very same two-index
placements, parent and orientation.  All raw channels up to D survive
in the child and enter their actual old parent word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedPairTicket
open Filter Function Finset Spec Extraction Table OPE OPE.Orbits OPE.Log OPE.Arboreal OPE.Nesting OPE.Nesting.Tree
open WilsonCenteredNestedTwoVertex WilsonCenteredNestedPairConvoy WilsonThermometerWeakPairFork
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def whole (p : Fin 5→C.book.Token) (w : Mode F.sector.derivatives) (X : Fin 5→E4) :=
  coalesce Q.port frame.leaves X p frame.root w

def tree (p : Fin 5→C.book.Token) (w : Mode F.sector.derivatives) (D : ℕ) (X : Fin 5→E4) :=
  ∑ j∈bands F.sector.derivatives D,coalesce Q.port WilsonThermometerWeakPairRooms.near X p 1 j *
    coalesce Q.port WilsonThermometerWeakPairRooms.outside X (update p 1 (Q.port.letter j)) frame.root w

theorem original (fac : Facilities C f S) {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (p : Fin 5→C.book.Token)
    (w : Mode F.sector.derivatives) (D : ℕ) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃ j : ℕ,∀ᶠ r:ℝ in 𝓝[>]0,∀(a:ℝ)(z:full.Plot),Accept r M η (dates r a) z →
      ∀ k:Ortho,
        WilsonThermometerWeakPairRooms.mass p a r / r^w.1 *
          ‖whole F Q p w (Ortho.move k ∘ sites z) - tree F Q p w D (Ortho.move k ∘ sites z)‖ ≤
        ((1+OPE.run r)*(1+OPE.run a))^j * (a/r)^(D+1) := by
  have bank := tickets_suffice F fac lo ticket Q.spans
  obtain ⟨j,issued⟩ := WilsonThermometerWeakNestedChild.original F bank frame p w (fun _=>D) 1 middle M η Mn ηp
  refine ⟨j,?_⟩
  filter_upwards [issued] with r statement a z room k
  have actual := WilsonCenteredNestedPairConvoy.original Mn room
  have row := statement (Ortho.move k ∘ sites z) (radius a r) rfl (rotated actual k)
  have held (de:DecidableEq (Fin 5)) : frame.live (@Finset.erase (Fin 5) de frame.zones 1)=WilsonThermometerWeakPairRooms.outside := by
    have same : de=instDecidableEqFin 5 := Subsingleton.elim _ _
    rw [same]
    exact pruned
  rw [WilsonThermometerWeakPairRooms.fee,WilsonThermometerWeakPairRooms.prestige,WilsonThermometerWeakPairRooms.ratio,WilsonThermometerWeakPairFork.inputs,held] at row
  unfold whole tree
  convert row using 1
  congr 3
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg₂ (·*·)
  · rfl
  · apply congrArg (fun pp => coalesce Q.port WilsonThermometerWeakPairRooms.outside (Ortho.move k ∘ sites z) pp frame.root w)
    funext i
    by_cases h:i=1
    · subst i;simp
    · simp [h]

end YM.Integration.WilsonCenteredNestedPairTicket
