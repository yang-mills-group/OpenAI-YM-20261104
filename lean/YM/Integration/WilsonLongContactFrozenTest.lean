import YM.Integration.WilsonLongContactSectorSeat

/-! A single paid physical leaf, frozen in the coarse test variables. Its whole
occupied fine test can be arbitrary bounded Borel on its original address. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactFrozenTest
open Lattice Wilson RG PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open ConnectedActivityE6.Blaze WilsonLongContactSectorSeat
open MeasureTheory
open scoped Classical BigOperators ContDiff
variable {G : Gauge} {n : Side} {Q : Rep G n}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rows (L : Leaf Q) (N : ℕ) (o : E) :
    ∃ l : ℕ, ∃ (T : Fin l → E → ℝ) (V : Fin l → Config G n → ℝ),
      (∀ (x : E) (U : Config G n), L.ingredient U=∑ i,T i x*V i U) ∧
      ∀ i, ContDiffAt ℝ (N:WithTop ℕ∞) (T i) o ∧ Measurable (V i) ∧
        ∃ b : ℝ,∀ U,‖V i U‖≤b := by
  refine ⟨1,fun _ _=>1,fun _=>L.ingredient,?_,?_⟩
  · intro x U
    simp
  · intro i
    exact ⟨contDiffAt_const,L.borel,L.weight,L.earn⟩

theorem current (L : Leaf Q) (N : ℕ) (o : E) (U : Config G n) :
    Brush N L.weight 1 (fun _ : E=>L.ingredient U) o :=
  (Brush.certified zero_le_one (L.ingredient U)).climb (L.earn U) le_rfl

theorem tested (L : Leaf Q) (N : ℕ) {I : Type*} (field : I → Config G n) (o : E) :
    LocalOn (RG.inspected L.crest) L.ingredient ∧
    (∀ t, Brush N L.weight 1 (fun _ : E=>L.ingredient (field t)) o) :=
  ⟨L.specific,fun t=>current L N o (field t)⟩

end YM.Integration.WilsonLongContactFrozenTest
