import YM.Integration.WilsonMaxwellThermometerChiralReading
import YM.XSpace.Tones

/-! The source normalization of the actual anti-self-dual thermometer legs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerOriginalChirality
open Lattice Maxwell Maxwell.Free XSpace.Chiral WilsonMaxwellThermometerChiralSlots
open WilsonMaxwellThermometerRotations WilsonMaxwellThermometerChiralReading
open scoped BigOperators

private def tile : Fin 6 → PlaqAxes := ![
  ⟨(0,1), by decide⟩,⟨(0,2), by decide⟩,⟨(0,3), by decide⟩,
  ⟨(2,3), by decide⟩,⟨(1,3), by decide⟩,⟨(1,2), by decide⟩]
private def listing : Fin 6 ≃ PlaqAxes := Equiv.ofBijective tile (by decide)
private def coefficient (s : Bool) (a : P) (i : Fin 6) : ℤ :=
  if i.val=a.val then 1 else if i.val=a.val+3 then (if a=1 then -phase s else phase s) else 0
private theorem original_row : ∀ (s : Bool) (a : P) (i : Fin 6),
    triCoeff s a (six (tile i)) (endr (tile i)) = coefficient s a i := by decide

theorem filed (s : Bool) (a : P) : Fq s a = slot s a := by
  rw [Fq, ← Equiv.sum_comp listing]
  change (∑ i : Fin 6, (triCoeff s a (six (tile i)) (endr (tile i)) : ℝ) •
    cell (six (tile i)) (endr (tile i))) = _
  simp only [original_row]
  rw [slot, ← phase_cast]
  fin_cases a <;> cases s <;>
    norm_num [Fin.sum_univ_succ, tile, six, endr, coefficient, phase, shard] <;>
    first | rfl | (change cell 1 3 = (-1:ℝ) • cell 3 1; rw [cell_skew 3 1]; module) |
      (change (-1:ℝ) • cell 1 3 = cell 3 1; rw [cell_skew 3 1]; module)

theorem original (G : Gauge) : U G = (2:ℂ)⁻¹ • polar G false := by
  rw [understand]; simp only [filed]; rfl

end YM.Integration.WilsonMaxwellThermometerOriginalChirality
