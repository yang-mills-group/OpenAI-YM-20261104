import YangMills.CorrelationHierarchy

/-! Microscopic data on the Wilson law used by the ordered limit. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Wilson

open Filter
open scoped BigOperators Topology

/-- Pure Yang--Mills one-loop beta coefficient for the same normalized matrix
trace used by `wilsonEnergy`. The basis of the public color space is orthonormal. -/
def wilsonOneLoop {g : GaugeGroup} (B : Maxwell.Reference g) : ℝ :=
  let E (i : Fin B.m) := B.matrix (EuclideanSpace.single i 1)
  let bracket (i j : Fin B.m) := E i * E j - E j * E i
  let casimir := (∑ i : Fin B.m, ∑ j : Fin B.m, -((bracket i j * bracket i j).trace).re) /
    (((g.n + 1 : ℕ) : ℝ) * (B.m : ℝ))
  11 * casimir / (48 * Real.pi ^ 2)

def timeMirror {l : ℕ+} (x : Site l) : Site l :=
  fun i => if i = timeAxis then -x i else x i

/-- Pullback of positive oriented bonds by the Euclidean time mirror. -/
def timeMirrorLinks {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) : Configuration g l :=
  fun e => if e.2 = timeAxis
    then (U (timeMirror e.1 - Pi.single e.2 1, e.2))⁻¹
    else U (timeMirror e.1, e.2)

/-- The finite raw coefficient space is fixed separately for each engineering cap. -/
abbrev RawSpace (width : ℕ) := Fin width → ℂ

/-- A common presentation of the microscopic insertions, including the finite-volume
unit. Its coordinate maps are chosen before the requested volume sequences. -/
structure GradedTokens {g : GaugeGroup} (C : WilsonFamily g)
    (conjugate starToken : C.Token → C.Token) where
  width : ℕ → ℕ
  token : (Σ d : ℕ, RawSpace (width d)) → C.Token
  onto : Function.Surjective token
  linear (N p d : ℕ) (x : Site (C.period p * C.denominator N))
      (U : Configuration g (C.period p * C.denominator N)) :
    IsLinearMap ℂ (fun v : RawSpace (width d) => C.insertion N p (token ⟨d,v⟩) x U)
  bar (d : ℕ) : RawSpace (width d) →ₛₗ[starRingEnd ℂ] RawSpace (width d)
  os (d : ℕ) : RawSpace (width d) →ₛₗ[starRingEnd ℂ] RawSpace (width d)
  tokenBar (d : ℕ) (v : RawSpace (width d)) : token ⟨d,bar d v⟩ = conjugate (token ⟨d,v⟩)
  tokenOS (d : ℕ) (v : RawSpace (width d)) : token ⟨d,os d v⟩ = starToken (token ⟨d,v⟩)
  unit : RawSpace (width 4)
  unitFinite : ∀ᶠ N : ℕ in atTop, ∀ p x U, C.insertion N p (token ⟨4,unit⟩) x U = 1

/-- Finite-volume insertions, their adjoints and the logarithmic running of the bare Wilson parameter. -/
structure WilsonData {g : GaugeGroup} (B : Maxwell.Reference g) (C : WilsonFamily g) where
  regular : WilsonRegularity C
  positive : 0 < wilsonOneLoop B
  running (ε : ℝ) : 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ p,
    |C.beta N p / Real.log ((C.mesh N)⁻¹) - 2 * wilsonOneLoop B| < ε
  translate (N p : ℕ) (v : C.Token) (x b : Site (C.period p * C.denominator N))
      (U : Configuration g (C.period p * C.denominator N)) :
    C.insertion N p v (x + b) U = C.insertion N p v x (fun e => U (e.1 + b, e.2))
  conjugate : C.Token → C.Token
  conjugate_involutive : Function.Involutive conjugate
  starToken : C.Token → C.Token
  star_involutive : Function.Involutive starToken
  reality (v : C.Token) : ∀ᶠ N : ℕ in atTop, ∀ p x U,
    C.insertion N p (conjugate v) x U = star (C.insertion N p v x U)
  reflection (v : C.Token) : ∀ᶠ N : ℕ in atTop, ∀ p x U,
    C.insertion N p (starToken v) (timeMirror x) U =
      star (C.insertion N p v x (timeMirrorLinks U))
  raw : GradedTokens C conjugate starToken

namespace WilsonData

variable {g : GaugeGroup} {B : Maxwell.Reference g} {C : WilsonFamily g}
def physicalLabel (T : Hierarchy C) (v : C.Token) : T.labels.carrier :=
  T.toLabel (T.project v).1 (T.project v).2

/-- Every physical field at each grade comes from a microscopic token. Its
OS adjoint includes both time reflection on tensor indices and conjugation. -/
structure AdjointOn (D : WilsonData B C) (T : Hierarchy C) : Prop where
  covers : Function.Surjective T.project
  respects (v : C.Token) :
    physicalLabel T (D.starToken v) = T.theory.adjointLabel (physicalLabel T v)
  quotient (d : ℕ) : ∃ π : RawSpace (D.raw.width d) →ₗ[ℂ] T.Field d,
    ∀ v, T.project (D.raw.token ⟨d,v⟩) = ⟨d,π v⟩
  unitProjects : T.project (D.raw.token ⟨4,D.raw.unit⟩) = ⟨4,T.unitAtFour⟩

end WilsonData
end YangMills.Wilson
