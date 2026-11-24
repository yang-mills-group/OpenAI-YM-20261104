import FormalConversion

/-! Finite position measurements and the free Maxwell Jacobian. Each reading
uses finitely many specified profiles and field tuples at a fixed cutoff. -/

set_option autoImplicit false
noncomputable section
namespace YangMills.MSbar.Position

open MeasureTheory
open scoped BigOperators Classical Distributions

variable {g : GaugeGroup}

abbrev Report (B : Maxwell.Reference g) (d : ℕ) :=
  (n : ℕ) → SeparatedTest n → (Fin n → B.sector d) → ℂ

/-- The linear test and multilinear field reports on which a position scheme
must commute with field parity and cutoff restriction. -/
def Lawful {B : Maxwell.Reference g} {d : ℕ} (Q : Report B d) : Prop :=
  ∀ n, ∃ L : SeparatedTest n →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => B.sector d) ℂ,
    ∀ t p, Q n t p = L t p

/-- The Wick moments smeared against each separated test. -/
def free (B : Maxwell.Reference g) (d : ℕ) : Report B d :=
  fun _ t p => ∫ x, t x * B.moment x (fun i => (p i).val)

def variation {B : Maxwell.Reference g} {d : ℕ} (Q : Report B d)
    (A : Module.End ℂ (B.sector d)) : Report B d :=
  fun n t p => ∑ i : Fin n, Q n t (Function.update p i (A (p i)))

/-- All admissible infinitesimal changes of the raw position frame through
cutoff d. This includes mixing from one engineering weight into lower ones. -/
structure IsChange (B : Maxwell.Reference g) (d : ℕ)
    (A : Module.End ℂ (B.sector d)) : Prop where
  unit (p : B.sector d) : p.val = 1 → A p = 0
  filtration (e : ℕ) (he : e ≤ d) (p : B.sector d) :
    p.val ∈ B.sector e → (A p).val ∈ B.sector e
  real (p : B.sector d) : (∀ m, (MvPolynomial.coeff m p.val).im = 0) →
    ∀ m, (MvPolynomial.coeff m (A p).val).im = 0
  signedAxes (σ : Equiv.Perm Axis) (sign : Axis → ℝ) (U : Spacetime ≃ₗᵢ[ℝ] Spacetime)
      (hsign : ∀ a, sign a = 1 ∨ sign a = -1)
      (hU : ∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1)
      (p q : B.sector d) : Matching.RelatedByAxes B σ sign U p.val q.val →
        Matching.RelatedByAxes B σ sign U (A p).val (A q).val

structure Window (B : Maxwell.Reference g) (d : ℕ) where
  arity : ℕ
  profile : SeparatedTest arity
  fields : Fin arity → B.sector d

/-- The real combinations of complex observations take values in the
finite-dimensional space of endomorphisms of this engineering cutoff. -/
structure Screen (B : Maxwell.Reference g) (d : ℕ) where
  size : ℕ
  window : Fin size → Window B d
  weights : (Fin size → ℂ) →ₗ[ℝ] Module.End ℂ (B.sector d)

def Screen.read {B : Maxwell.Reference g} {d : ℕ} (S : Screen B d)
    (Q : Report B d) : Module.End ℂ (B.sector d) :=
  S.weights fun i => Q (S.window i).arity (S.window i).profile (S.window i).fields

/-- Negating every free curvature jet acts on a monomial by the parity of
its number of curvature factors, independently of its engineering weight. -/
def Mirrored (B : Maxwell.Reference g) (p q : B.toCoordinates.Pol) : Prop :=
  ∀ x : B.toCoordinates.Tower,
    B.toCoordinates.eval x q = B.toCoordinates.eval (fun j => -x j) p

/-- The finite system recovers every allowed tangent from free moments.
Restriction and field parity concern its numerical readings on all multilinear
reports, including those away from the free model. -/
structure Prepared {B : Maxwell.Reference g} (screen : (d : ℕ) → Screen B d) : Prop where
  range (d : ℕ) (v : Fin (screen d).size → ℂ) :
    IsChange B d ((screen d).weights v)
  tangent (d : ℕ) (A : Module.End ℂ (B.sector d)) :
    IsChange B d A → (screen d).read (variation (free B d) A) = A
  nested (d : ℕ) (Q : Report B d) (R : Report B (d+1)) :
    Lawful Q → Lawful R →
    (∀ (n : ℕ) (t : SeparatedTest n) (p : Fin n → B.sector d) (q : Fin n → B.sector (d+1)),
      (∀ i, (p i).val = (q i).val) → Q n t p = R n t q) →
    ∀ (p : B.sector d) (q : B.sector (d+1)), p.val = q.val →
      ((screen d).read Q p).val = ((screen (d+1)).read R q).val
  parity (d : ℕ) (Q R : Report B d) : Lawful Q → Lawful R →
    (∀ (n : ℕ) (t : SeparatedTest n) (p q : Fin n → B.sector d),
      (∀ i, Mirrored B (p i).val (q i).val) → Q n t p = R n t q) →
    ∀ (p q : B.sector d), Mirrored B p.val q.val →
      Mirrored B ((screen d).read Q p).val ((screen d).read R q).val

end YangMills.MSbar.Position
