import YangMills.MatrixGauge
import YangMills.LatticeFields
import YM.Extraction.LatticeFamily

/-! The microscopic family and its native coordinates for graded insertions. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.PerturbativeMatching
open MeasureTheory
variable {g : GaugeGroup} {C : WilsonFamily g}

def wilsonFamily (C : YM.Family g.core) : WilsonFamily g where
  period := C.S.period
  denominator := C.S.denominator
  periodStrict := C.S.period_strict
  denominatorStrict := C.S.den_strict
  beta := C.beta
  haar := g.core.probHaar
  probability := inferInstanceAs (IsProbabilityMeasure g.core.probHaar)
  invariantHaar := inferInstanceAs g.core.probHaar.IsHaarMeasure
  Token := C.book.Token
  insertion N p v x := C.seen (N := N) (p := p) v x

/-- The raw coordinates used to lift continuum fields are the coefficient
vectors of the original graded lattice insertions, in their original order. -/
def NativeCoordinates {B : Maxwell.Reference g} (lattice : YM.Family g.core)
    (data : Wilson.WilsonData B (wilsonFamily lattice)) : Prop :=
  ∃ widths : ∀ d, data.raw.width d = (lattice.labels.level d).extra + 1,
    ∀ (d : ℕ) (v : Wilson.RawSpace (data.raw.width d)),
      data.raw.token ⟨d, v⟩ = ⟨d, fun i => v (Fin.cast (widths d).symm i)⟩

/-- The measured family comes from admissible Wilson lattice data with the native
coordinate metric used to lift its physical fields. -/
def AdmissibleLattice {B : Maxwell.Reference g} (data : Wilson.WilsonData B C) : Prop :=
  ∃ lattice : YM.Family g.core, ∃ same : wilsonFamily lattice = C,
    lattice.Makes ∧ NativeCoordinates lattice (same.symm ▸ data)

end YangMills.PerturbativeMatching
