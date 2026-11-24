import YM.Integration.WilsonMixedFaceLog
import YM.Integration.WilsonOriginalProjectedCurvatureTableau

/-! One actual test wallet for the occupied old and fresh faces, with their independently submitted real kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMixedTestTableau
open Finset Function Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open WilsonMixedPassportRows
open scoped Classical

variable {V : Type} [DecidableEq V] {E F : V → Type}
  [∀ v, AddCommGroup (E v)] [∀ v, AddCommGroup (F v)] [∀ v, Module ℝ (E v)] [∀ v, Module ℝ (F v)]
  (A : ∀ v, Set (E v)) (B : ∀ v, Set (F v))
  (K : ∀ v, Submodule ℝ (E v)) (L : ∀ v, Submodule ℝ (F v))

def actors (v : V) : Set (E v × F v) := (A v) ×ˢ (B v)
def pieces (v : V) : Submodule ℝ (E v × F v) := (K v).prod (L v)

def pair (x : Wallet A) (y : Wallet B) : Wallet (actors A B) :=
  fun v => ⟨((x v).val, (y v).val), (x v).property, (y v).property⟩

def leftAt (old : Finset V) (zero : ∀ v, 0 ∈ A v) (v : V) (a : actors A B v) : A v :=
  if v ∈ old then ⟨a.val.1, a.property.1⟩ else ⟨0, zero v⟩

def rightAt (fresh : Finset V) (zero : ∀ v, 0 ∈ B v) (v : V) (a : actors A B v) : B v :=
  if v ∈ fresh then ⟨a.val.2, a.property.2⟩ else ⟨0, zero v⟩

def left (old : Finset V) (zero : ∀ v, 0 ∈ A v) (x : Wallet (actors A B)) : Wallet A :=
  fun v => leftAt A B old zero v (x v)
def right (fresh : Finset V) (zero : ∀ v, 0 ∈ B v) (x : Wallet (actors A B)) : Wallet B :=
  fun v => rightAt A B fresh zero v (x v)

private theorem transport {X Y : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, AddCommGroup (Y v)]
    [∀ v, Module ℝ (X v)] [∀ v, Module ℝ (Y v)]
    {a : ∀ v, Set (X v)} {b : ∀ v, Set (Y v)} {k : ∀ v, Submodule ℝ (X v)} {l : ∀ v, Submodule ℝ (Y v)}
    {s : Finset V} {f : Wallet a → ℂ} (H : Attn k a s f) (project : ∀ v, b v → a v)
    (turn : ∀ i ∈ s, ∀ (u v w : b i) (c d : ℝ), w.val = c • u.val + d • v.val →
      (project i w).val = c • (project i u).val + d • (project i v).val)
    (idle : ∀ i ∈ s, ∀ t : b i, t.val ∈ l i → (project i t).val ∈ k i) :
    Attn l b s (fun t => f (fun i => project i (t i))) := by
  have update (t : Wallet b) (i : V) (z : b i) :
      (fun v => project v (Function.update t i z v)) = Function.update (fun v => project v (t v)) i (project i z) := by
    funext v
    by_cases atSite : v = i
    · subst v
      simp only [Function.update_self]
    · simp only [Function.update_of_ne atSite]
  constructor
  · intro t u agree
    exact H.sit _ _ (fun i hi => congrArg (project i) (agree i hi))
  · intro i hi t x y z c d equation
    rw [update t i z, update t i x, update t i y]
    exact H.turns i hi _ _ _ _ _ _ (turn i hi x y z c d equation)
  · intro i hi t belongs
    exact H.idle i hi _ (idle i hi (t i) belongs)

variable {G : Gauge} {n : Side} {C : Census V} {P Q : Passport n V} {ι κ : Type}
  (M : ι → Row P C G (Wallet A)) (Y : κ → Row Q C G (Wallet B)) (old fresh : Finset V) (sep : Disjoint old fresh)
  (zeroA : ∀ v, 0 ∈ A v) (zeroB : ∀ v, 0 ∈ B v)

/-- The old and fresh real linear tests remain tied to their own charged labels inside the full reported roster. -/
theorem original (oldFile : Tableau K A M) (newFile : Tableau L B Y) :
    Tableau (pieces K L) (actors A B)
      (WilsonMixedFaceLog.routed M Y old fresh sep (left A B old zeroA) (right A B fresh zeroB)) := by
  constructor
  rintro (i | i)
  · apply transport (oldFile.bill i.val) (leftAt A B old zeroA)
    · intro j belongs x y z c d eq
      simp only [leftAt, if_pos (i.property belongs)]
      exact congrArg Prod.fst eq
    · intro j belongs t nil
      simp only [leftAt, if_pos (i.property belongs)]
      exact nil.1
  · apply transport (newFile.bill i.val) (rightAt A B fresh zeroB)
    · intro j belongs x y z c d eq
      simp only [rightAt, if_pos (i.property belongs)]
      exact congrArg Prod.snd eq
    · intro j belongs t nil
      simp only [rightAt, if_pos (i.property belongs)]
      exact nil.2

end YM.Integration.WilsonMixedTestTableau
