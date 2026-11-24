import MSPositionPrescription

/-! The position frame in the raw MS coupling. At order k+1 the terms
with one new field coefficient are the first variation of the free Maxwell
moments. All other terms use the coefficients through k. The fixed screen's
left inverse reads the required correction from those remaining terms. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.MSbar.Position

open MeasureTheory
open scoped BigOperators Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g}

abbrev EndAt (B : Maxwell.Reference g) (d : ℕ) := Module.End ℂ (B.sector d)

/-- Degree k of the MS moment with one formal field map inserted on every
leg. Only coefficients of the map through degree r participate. -/
def momentThrough (M : Coefficients B) (d k r : ℕ)
    (A : Fin (r + 1) → EndAt B d) (n : ℕ) (v : Fin n → B.sector d)
    (x : Points n) : ℂ :=
  ∑ ν : Fin n → Fin (r + 1),
    let used := ∑ i, (ν i).val
    if used ≤ k then
      M.correlation n (k - used) (fun i => ⟨d, A (ν i) (v i)⟩) x
    else 0

/-- The known order-(k+1) source term. Truncating every input at k omits
precisely the individual new-leg insertions against the Maxwell tree. -/
def residualReport (M : Coefficients B) (d k : ℕ)
    (A : Fin (k + 1) → EndAt B d) : Report B d :=
  fun n φ v => ∫ x, φ x * momentThrough M d (k + 1) k A n v x

/-- Extend a single prefix in the original MS variable. The order-zero field
map is the identity. At each subsequent order the minus sign cancels the
known residual in the fixed position measurements. -/
def framePrefix (M : Coefficients B) (P : PositionPrescription B) (d : ℕ) :
    (k : ℕ) → Fin (k + 1) → EndAt B d
  | 0 => fun _ => LinearMap.id
  | k + 1 =>
    let previous := framePrefix M P d k
    Fin.lastCases (-(P.screen d).read (residualReport M d k previous)) previous

/-- The coefficient of the initial position-frame normalization at this order,
before the triangle coupling substitution and the homogeneous adjustment. -/
def rawFrame (M : Coefficients B) (P : PositionPrescription B) (d k : ℕ) : EndAt B d :=
  framePrefix M P d k (Fin.last k)

@[simp] theorem rawFrame_zero (M : Coefficients B) (P : PositionPrescription B) (d : ℕ) :
    rawFrame M P d 0 = LinearMap.id := rfl

/-- Increasing the order retains every previously computed coefficient. -/
theorem framePrefix_coeff (M : Coefficients B) (P : PositionPrescription B)
    (d k : ℕ) (i : Fin (k + 1)) : framePrefix M P d k i = rawFrame M P d i.val := by
  induction k with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rfl
  | succ k ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · simpa [framePrefix] using ih j

theorem rawFrame_succ (M : Coefficients B) (P : PositionPrescription B) (d k : ℕ) :
    rawFrame M P d (k + 1) = -(P.screen d).read (residualReport M d k (framePrefix M P d k)) := by
  simp [rawFrame, framePrefix]

/-- Every nonconstant coefficient belongs to the prescribed tangent space. -/
theorem rawFrame_change (M : Coefficients B) (P : PositionPrescription B)
    (hP : Prepared P.screen) (d k : ℕ) : IsChange B d (rawFrame M P d (k + 1)) := by
  let S := P.screen d
  let Q := residualReport M d k (framePrefix M P d k)
  let v (i : Fin S.size) := Q (S.window i).arity (S.window i).profile (S.window i).fields
  have permitted := hP.range d (-v)
  have eq : S.weights (-v) = -(S.weights v) := by
    calc
      S.weights (-v) = S.weights ((-1 : ℝ) • v) :=
        congrArg S.weights (neg_one_smul ℝ v).symm
      _ = (-1 : ℝ) • S.weights v := S.weights.map_smul (-1) v
      _ = -(S.weights v) := neg_one_smul ℝ (S.weights v)
  rw [rawFrame_succ]
  exact eq ▸ permitted

/-- The recurrence solves the finite Jacobian equations at every positive order. -/
theorem rawFrame_balances (M : Coefficients B) (P : PositionPrescription B)
    (hP : Prepared P.screen) (d k : ℕ) :
    (P.screen d).read (variation (free B d) (rawFrame M P d (k + 1))) +
      (P.screen d).read (residualReport M d k (framePrefix M P d k)) = 0 := by
  rw [hP.tangent d _ (rawFrame_change M P hP d k), rawFrame_succ]
  exact neg_add_cancel ((P.screen d).read (residualReport M d k (framePrefix M P d k)))

/-- The pointwise coefficient used for the connected triangle. All factors
in each product are evaluated on the same configuration before smearing. -/
def rawMoment (M : Coefficients B) (P : PositionPrescription B) (d k n : ℕ)
    (v : Fin n → B.sector d) (x : Points n) : ℂ :=
  momentThrough M d k k (framePrefix M P d k) n v x

def rawReport (M : Coefficients B) (P : PositionPrescription B) (d k : ℕ) : Report B d :=
  fun n φ v => ∫ x, φ x * rawMoment M P d k n v x

/-- The first-variation rank condition makes each correction unique among
the permitted real, symmetry-preserving, filtration-preserving changes. -/
theorem uniqueStep (M : Coefficients B) (P : PositionPrescription B) (d k : ℕ)
    (leftInverse : ∀ A : EndAt B d, IsChange B d A →
      (P.screen d).read (variation (free B d) A) = A)
    (A : EndAt B d) (permitted : IsChange B d A)
    (balances : (P.screen d).read (variation (free B d) A) +
      (P.screen d).read (residualReport M d k (framePrefix M P d k)) = 0) :
    A = rawFrame M P d (k + 1) := by
  rw [leftInverse A permitted] at balances
  rw [rawFrame_succ]
  exact @eq_neg_of_add_eq_zero_left (EndAt B d) _ A _ balances

/-- The checks are on the computed coefficients and full normalized moments.
Integrability is required for each integral used by the finite recursion. -/
structure RawValid (M : Coefficients B) (P : PositionPrescription B) : Prop where
  tree (n d : ℕ) (v : Fin n → B.sector d) (x : Points n) (hx : x ∈ separated n) :
    M.correlation n 0 (fun i => ⟨d, v i⟩) x = B.moment x (fun i => (v i).val)
  nested (d e k : ℕ) (p : B.sector d) (q : B.sector e) :
    p.val = q.val → (rawFrame M P d k p).val = (rawFrame M P e k q).val
  residualIntegrable (d k n : ℕ) (φ : SeparatedTest n) (v : Fin n → B.sector d) :
    Integrable (fun x => φ x * momentThrough M d (k + 1) k (framePrefix M P d k) n v x)
  integrable (d k n : ℕ) (φ : SeparatedTest n) (v : Fin n → B.sector d) :
    Integrable (fun x => φ x * rawMoment M P d k n v x)
  normalized (d k : ℕ) :
    (P.screen d).read (rawReport M P d k) =
      if k = 0 then (P.screen d).read (free B d) else 0

end YangMills.MSbar.Position
