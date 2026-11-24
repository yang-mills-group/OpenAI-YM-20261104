import YM.RG06.Weak.Coeffs
import YM.Pert.Lattice.Plate
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Kinematic log-link and path letters, actual YM matrix convention

`cycle` reads a list-order holonomy in traversal order; reversed links
pay conjugate transpose. Independent coefficients are finite noncommutative
Cauchy products (we leave G.Mat as the actual matrix algebra over ℂ, with
Frobenius norms). They can be requested at any fixed degree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Weak
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
open Lattice NormedSpace Function
variable {G : Gauge}

def letter (A : G.Color) (n : ℕ) := (n.factorial:ℝ)⁻¹ • G.colorMat A ^ n

def read (A : G.Color) (t : ℝ) := G.mat (G.lieExp (t • A))

lemma matrix_reads_smooth (A : G.Color) : ContDiff ℝ ∞ (read A) := by
  unfold read; simp only [G.mat_lieExp,map_smul]; exact G.contDiff_exp.of_le (show ∞ ≤ ω from le_top) |>.comp (contDiff_id.smul contDiff_const)

lemma matrix_reads_deriv (A : G.Color) (t : ℝ) : HasDerivAt (read A) (read A t * G.colorMat A) t := by
  rw [show read A = (fun t : ℝ=> exp (t • G.colorMat A)) by funext t; rw [read,G.mat_lieExp,map_smul]]
  exact hasDerivAt_exp_smul_const ..

lemma matrix_reads_jet (A : G.Color) (n : ℕ) : iteratedDeriv n (read A)= fun t=>read A t * G.colorMat A^n := by
  induction n with
  | zero=>simp
  | succ n h=>
    rw [iteratedDeriv_succ,h]
    funext t
    rw [((matrix_reads_deriv A t).mul_const _).deriv,pow_succ',mul_assoc]

lemma matrix_reads (A : G.Color) : Writes (read A) (letter A) where
  smooth := (matrix_reads_smooth A).contDiffAt
  coeff n := by rw [matrix_reads_jet]; simp [read,letter]

def back (F : ℕ→G.Mat) (n : ℕ) := star (F n)

def turn (s : Bool) (F : ℕ → G.Mat) := if s then back F else F

lemma Writes.backwards {p : ℝ→G.El} {F : ℕ→ G.Mat} (h : Writes (G.mat ∘ p) F) : Writes (fun t : ℝ=> G.mat ((p t)⁻¹)) (back F) := by
  simp_rw [G.mat_inv]; let Z : G.Mat →L[ℝ] G.Mat:= (starL ℝ).toContinuousLinearMap
  exact h.apply Z

lemma Writes.reverse {p : ℝ→G.El} {F : ℕ→ G.Mat} (h : Writes (G.mat ∘ p) F) (s : Bool) : Writes (fun t : ℝ=> G.mat (if s then ((p t)⁻¹) else p t)) (turn s F) := by
  cases s <;> simp only [Bool.false_eq_true,↓reduceIte,turn]; exacts [h,h.backwards]

lemma back_letter (x : G.Color) (n : ℕ) : back (letter x) n = letter (-x) n := by
  simp only [back,letter,star_smul,star_trivial,star_pow,G.colorMat_skew,map_neg]

section Path
variable {R : Type*} [AddCommGroup R] [One R]

def ray (a : Links R G.Color) (t : ℝ) : Links R G.El := fun i=> G.lieExp (t • a i)

def cycleWith (F : Links R (ℕ → G.Mat)) (x : Four R) : Walk → ℕ → G.Mat
  | []=> seed 1
  | d::k => join (turn d.neg (F (d.used x))) (cycleWith F (x+d.vec) k)

lemma Step.at_used (d : Lattice.Step) (U : Links R G.El) (x : Four R) : d.read U x = (if d.neg then (U (d.used x))⁻¹ else U (d.used x)) := by
  cases h:d.neg <;> simp only [Lattice.Step.read,Lattice.Step.used,h,Bool.false_eq_true, ↓reduceIte]

lemma Writes.travel {f : ℝ → Links R G.El} {F : Links R (ℕ → G.Mat)} (h : ∀ i,Writes (fun t=>G.mat (f t i)) (F i))
    (x : Four R) (k : Walk) : Writes (fun t=>G.mat (travel (f t) x k)) (cycleWith F x k) := by
  induction k generalizing x with
  | nil=>simp_rw [cycleWith,Lattice.travel,G.mat_one]; exact Writes.constant _
  | cons d l ih=>
    simp_rw [cycleWith,Lattice.travel,G.mat_mul,Step.at_used]
    exact ((h (d.used x)).reverse d.neg).times (ih _)

def tile (a : Links R G.Color) : Links R (ℕ→G.Mat) := fun i=>letter (a i)
def cycle (a : Links R G.Color) := cycleWith (tile a)

theorem cycle_reads (a : Links R G.Color) (x : Four R) (k : Walk) :
    Writes (fun t : ℝ=>G.mat (travel (ray a t) x k)) (cycle a x k) :=
  Writes.travel (fun i=>matrix_reads (a i)) _ _

/-- Literal link inventory in traversal order, with repetitions and inverses.
Used to state support bounds without passing to a set of distinct edges first. -/
def inventory (x : Four R) : Walk→ List (Edge (Four R) × Bool)
  | [] => []
  | d::k => (d.used x,d.neg)::inventory (x+d.vec) k

@[simp] theorem inventory_length (x : Four R) (k : Walk) : (inventory x k).length=k.length := by
  induction k generalizing x with
  | nil=>rfl
  | cons d k ih=>simp [inventory,ih]

theorem cycle_contains {F H : Links R (ℕ→G.Mat)} (x : Four R) (k : Walk)
    (h : ∀ v∈inventory x k,F v.1=H v.1) : cycleWith F x k=cycleWith H x k:= by
  induction k generalizing x with
  | nil=>rfl
  | cons d k ih=>rw [cycleWith,cycleWith,h (d.used x,d.neg) (by simp [inventory]),ih _ (fun v hv=>h v (by simpa only [inventory,List.mem_cons] using Or.inr hv))]

end Path
end YM.RG06.Weak
