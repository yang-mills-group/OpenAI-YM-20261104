import YM.Integration.WilsonThermometerUnitFilingFourSquare

/-! A common reflected quadrature of the signed Wilson field difference. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourSquareGram
open Filter Extraction Spec Table
open WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {l : Filter (ℕ×ℕ)} [l.NeBot] {d : ℕ}

def pair (F : Final C f S) (s : Signed) {v w : S.Field d}
    (A : Bool → Arm C S l d v) (B : Bool → Arm C S l d w) (i : Fin 2) (b : Bool) :
    Arm C S l d (![S.mirror F.room.kernel.spin d s (S.conj F.room.kernel.spin d v),w] i) := by
  refine Fin.cases (motive:=fun j => Arm C S l d
    (![S.mirror F.room.kernel.spin d s (S.conj F.room.kernel.spin d v),w] j))
    (reflected F (A b) s) ?_ i
  intro j
  exact Fin.cases (motive:=fun j : Fin 1 => Arm C S l d
    (![S.mirror F.room.kernel.spin d s (S.conj F.room.kernel.spin d v),w] j.succ))
    (B b) (fun k => k.elim0) j

/-- The actual finite Wilson sums over both sets of placements, including
conjugated left weights. Each quartet shares its test and both dates. -/
theorem original (F : Final C f S) (order : l ≤ f.fuse) (s : Signed)
    {ι : Type*} (Q : Finset ι) (v : ι → S.Field d) (rows : ∀ j, Bool → Arm C S l d (v j))
    (a : ι → ℂ) (t : ι → ι → Test 2) :
    Tendsto (fun z => ∑ i ∈ Q, ∑ j ∈ Q, (star (a i)*a j) *
      contrast (pair F s (rows i) (rows j)) (t i j) z) l (𝓝 0) := by
  have each (i j : ι) := (WilsonThermometerUnitFilingFourSquare.original F order
    (pair F s (rows i) (rows j)) (t i j)).const_mul (star (a i)*a j)
  have row (i : ι) : Tendsto (fun z => ∑ j ∈ Q, (star (a i)*a j) *
      contrast (pair F s (rows i) (rows j)) (t i j) z) l (𝓝 0) := by
    simpa only [mul_zero,Finset.sum_const_zero] using tendsto_finsetSum Q (fun j _ => each i j)
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Q (fun i _ => row i)

end YM.Integration.WilsonThermometerUnitFilingFourSquareGram
