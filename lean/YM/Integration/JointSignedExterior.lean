import YM.Integration.JointSignedInitialization

/-!
Keep exterior observables in the same joint polynomial as an internal signed
comparison.  Each exterior region uses one visible product factor, explicit
unit factors in its other slots, and a zero counterterm.  This is an exact
specialization of the existing projection, not an estimate for the added
slots.  Any later rooted budget must account for this displayed alphabet.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.JointSignedInitialization
open Function Finset MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent Extra.Trajectories
open scoped BigOperators Classical

variable {I J E X : Type} [Fintype J] [DecidableEq J]

def exteriorFactors (j₀ : J) (F : I → J → X → ℂ) (D : E → X → ℂ) :
    I ⊕ E → J → X → ℂ :=
  Sum.elim F (fun e j U => if j = j₀ then D e U else 1)

def exteriorCounter (K : I → X → ℂ) : I ⊕ E → X → ℂ :=
  Sum.elim K (fun _ _ => 0)

/-- Exterior observables are retained literally, including their dependence
on the same field; no independence or locality of the full product is asserted. -/
theorem signed_exterior (j₀ : J) (F : I → J → X → ℂ)
    (K : I → X → ℂ) (D : E → X → ℂ) :
    signed (exteriorFactors j₀ F D) (exteriorCounter K) =
      Sum.elim (signed F K) D := by
  funext a U
  cases a with
  | inl i => rfl
  | inr e => simp [signed, exteriorFactors, exteriorCounter]

variable {G : Gauge} {n : Side}
    [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

/-- The complete internal/exterior polynomial still has one original vacuum. -/
theorem exterior_birth (R : Rep G n) (j₀ : J)
    (F : I → J → Config G n → ℂ) (K : I → Config G n → ℂ)
    (D : E → Config G n → ℂ) :
    (fun U => project (Accent.birth original R
      (sources (exteriorFactors j₀ F D) (exteriorCounter K)) U)) =
      Accent.birth grouped R (Sum.elim (signed F K) D) := by
  rw [project_birth, signed_exterior]

/-- Every exterior label is pushed jointly with the internal discrepancy.
The raw integrability premise concerns this complete original polynomial. -/
theorem exterior_gust (H : History G) (N p : ℕ) (j₀ : J)
    (F : I → J → Config G (H.S.side N p) → ℂ)
    (K : I → Config G (H.S.side N p) → ℂ)
    (D : E → Config G (H.S.side N p) → ℂ)
    (hP : Integrable (Accent.birth original (H.rep N p N)
      (sources (exteriorFactors j₀ F D) (exteriorCounter K)))
      (prior G (H.S.side N p))) {m : ℕ} (hm : m ≤ N) :
    gust H N p N (Accent.birth grouped (H.rep N p N)
      (Sum.elim (signed F K) D)) m hm =
      fun U => project (gust H N p N (Accent.birth original (H.rep N p N)
        (sources (exteriorFactors j₀ F D) (exteriorCounter K))) m hm U) := by
  rw [← signed_exterior j₀ F K D]
  exact signed_gust H N p _ _ hP hm

end YM.Integration.JointSignedInitialization
