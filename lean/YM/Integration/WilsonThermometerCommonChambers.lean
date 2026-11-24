import YM.Cells.Proximity
/-! One physical translation places all separated children in distinct
admissible chambers of the given original tiling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCommonChambers
open Lattice Cells Function
open scoped Classical
variable {n : Side} {k : ℕ}

theorem original (T : Tiling n) (x : Fin k → Site n) (B : ℕ) (positive : 0<B)
    (room : k*(2*B)<T.side.val)
    (different : ∀ i j : Fin k, i≠j→T.side.val<separation (x i) (x j)) :
    ∃ w : Site n, ∃ v : Fin k → T.Cell, Injective v ∧
      ∀ i, x i+w ∈ T.margin (v i) B := by
  obtain ⟨o,inside⟩ := T.fits_together x B positive room
  let v (i:Fin k) := (T.newly o).which (x i)
  refine ⟨T.base-o,v,?_,?_⟩
  · intro i j same
    by_contra unequal
    have hp : x j∈(T.newly o).chamber (v i) := same ▸ (inside j).1
    exact (not_le.mpr (different i j unequal)) ((T.newly o).extent (inside i).1 hp)
  · intro i
    have delta (a : Axis) : (x i+(T.base-o)) a-T.starts (v i) a =
        x i a-(T.newly o).starts (v i) a := by
      simp only [Tiling.starts,Tiling.newly,Pi.add_apply,Pi.sub_apply]
      abel
    constructor
    · intro a
      rw [delta]
      exact (inside i).1 a
    · intro a
      unfold Tiling.coordinated
      rw [delta]
      exact (inside i).2 a

end YM.Integration.WilsonThermometerCommonChambers
