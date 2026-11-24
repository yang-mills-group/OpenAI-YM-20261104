import YangMills.LatticeFields

set_option autoImplicit false
noncomputable section

namespace YangMills.Wilson.ObservablePhases

open Filter MeasureTheory
open scoped BigOperators Topology

variable {g : GaugeGroup} {B : Maxwell.Reference g} {C : WilsonFamily g}

abbrev Word (C : WilsonFamily g) := List (Spacetime × C.Token)

/-- Every finite list of pairwise distinct insertion sites, including the empty list. -/
abbrev SeparatedWord (C : WilsonFamily g) := {w : Word C // (w.map Prod.fst).Nodup}

/-- Read the microscopic tokens in the public hierarchy. -/
def read (T : Hierarchy C) (s : Option T.Character) (w : Word C) : ℂ :=
  T.correlation s (fun i : Fin w.length => T.project (w.get i).2)
    (WithLp.toLp 2 (fun i : Fin w.length => (w.get i).1))

def signature (T : Hierarchy C) (χ : T.Character) (w : SeparatedWord C) : ℂ :=
  read T (some χ) w.val

/-- The OS adjoint reverses the word and reflects both the sites and the tokens. -/
def reflected (D : WilsonData B C) (w : Word C) : Word C :=
  w.reverse.map fun p =>
    (WithLp.toLp 2 (fun a => if a = timeAxis then -p.1 a else p.1 a), D.starToken p.2)

/-- At gap n shift every site of cluster j by j*n in the positive Euclidean time
direction; take its genuine OS adjoint first if requested. -/
def train (D : WilsonData B C) {k : ℕ} (w : Fin k → SeparatedWord C)
    (adjoint : Fin k → Bool) (n : ℕ) : Word C :=
  (List.ofFn fun j : Fin k =>
    let v := if adjoint j then reflected D (w j).val else (w j).val
    let shift : Spacetime := EuclideanSpace.single timeAxis ((j.val : ℝ) * (n : ℝ))
    v.map fun p => (p.1 + shift, p.2)).flatten

/-- The measured characters of this Wilson hierarchy. The unselected reading of
one translated whole word fixes every joint moment of the phase readings and
their conjugates. The mesh and volume limits precede this separation limit. -/
structure Law (D : WilsonData B C) (T : Hierarchy C) : Prop where
  separates : Function.Injective (signature T)
  trains (k : ℕ) (w : Fin k → SeparatedWord C) (adjoint : Fin k → Bool) :
    Tendsto (fun n : ℕ => read T none (train D w adjoint n)) atTop
      (𝓝 (∫ χ, ∏ j, if adjoint j then star (signature T χ (w j))
                     else signature T χ (w j) ∂T.phaseMeasure))

end YangMills.Wilson.ObservablePhases
