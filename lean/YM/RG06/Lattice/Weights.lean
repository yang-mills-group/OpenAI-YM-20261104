import YM.RG06.Lattice.Curvature

/-!
# Fluctuation weights in the Wilson rule

Every coefficient (scalar/matrix) explicitly homogeneous in the bond logarithms. Includes zero
as a homogeneous polynomial in every weight (no converse implied).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.WilsonRules
open Lattice Wilson MvPolynomial RG
open scoped BigOperators
variable {G : Gauge} {X : Type*}

def legs (k : ℕ) (p : Feynman G X) := MvPolynomial.IsWeightedHomogeneous (fun _=> (1:ℕ)) p k

def legsM (k : ℕ) (p : PMat G X) := ∀ i j, legs k (p i j)

namespace Legs
variable {k l : ℕ} {p q : Feynman G X} {M N : PMat G X}
@[simp] lemma zero : legs k (0 : Feynman G X) := isWeightedHomogeneous_zero ℂ _ _
lemma add : legs k p → legs k q → legs k (p+q) := IsWeightedHomogeneous.add
lemma mul : legs k p → legs l q → legs (k+l) (p*q) := IsWeightedHomogeneous.mul
lemma neg (hp : legs k p) : legs k (-p) :=
  Submodule.neg_mem (MvPolynomial.weightedHomogeneousSubmodule ℂ (fun (_:Key G X)=> (1:ℕ)) k) hp
lemma sub (hp : legs k p) (hq : legs k q) : legs k (p-q) := by rw [sub_eq_add_neg]; exact add hp (neg hq)
lemma c_mul (a : ℂ) (hp : legs k p) : legs k (MvPolynomial.C a * p) := MvPolynomial.IsWeightedHomogeneous.C_mul hp _
lemma sum {I : Type*} (s : Finset I) (F : I → Feynman G X) (h : ∀ i∈s, legs k (F i)) : legs k (∑ i∈s,F i) :=
  IsWeightedHomogeneous.sum _ _ _ h

lemma mul_mat (hp : legsM k M) (hq : legsM l N) : legsM (k+l) (M*N) := by
  intro i j; rw [Matrix.mul_apply]; exact sum _ _ fun m _=> mul (hp i m) (hq m j)

lemma pow_mat (hp : legsM 1 M) (n : ℕ) : legsM n (M ^ n) := by
  induction n with
  | zero =>
    intro i j; rw [pow_zero,Matrix.one_apply]; split
    · exact isWeightedHomogeneous_one ℂ _
    exact zero
  | succ n ih => rw [pow_succ]; exact mul_mat ih hp
end Legs

lemma kick_legs (e : LogBond X) (b : Bool) (k : ℕ) : legsM k (PowerSeries.coeff k (kick G e b)) := by
  have hn (i j): legs 1 (generator G e i j):= by
    unfold generator; simp only [Matrix.of_apply]; refine Legs.sum _ _ fun a _=> ?_ 
    rw [mul_comm]; exact Legs.c_mul _ (isWeightedHomogeneous_X ℂ _ _)
  intro i j
  simp only [kick, PowerSeries.coeff_mk,Matrix.smul_apply, smul_eq_mul]
  apply Legs.c_mul
  cases b
  · exact Legs.pow_mat hn k i j
  exact Legs.pow_mat (M:=-generator G e) (fun a d=> Legs.neg (hn a d)) k i j

variable [AddCommGroup X] [One X]
lemma ordered_legs (x : Four X) (s : Walk) (k : ℕ) : legsM k (PowerSeries.coeff k (ordered G x s)) := by
  classical
  induction s generalizing x k with
  | nil =>
    intro i j
    simp only [ordered, PowerSeries.coeff_one]; split
    next h=>
      subst k; rw [Matrix.one_apply]; split
      · exact isWeightedHomogeneous_one ℂ _
      exact Legs.zero
    exact Legs.zero
  | cons d s ih =>
    intro i j; rw [ordered, PowerSeries.coeff_mul]
    simp only [Matrix.sum_apply]
    refine Legs.sum _ _ fun a ha=> ?_
    have he := Finset.mem_antidiagonal.mp ha
    exact he ▸ Legs.mul_mat (kick_legs (G:=G) (d.used x) d.neg a.1) (ih (x+d.vec) a.2) i j -- ▸ rewrites too much?

lemma slot_legs (s : Slot) (c : G.ColorIndex) (k : ℕ) : legs k (slotCoeff G s c k) := by
  have he (p : Walk) : legs k (colorTrace G c (PowerSeries.coeff k (ordered G (0:Cover) p))) := by
    unfold colorTrace Matrix.trace; apply Legs.sum _ _ fun i _=> ?_
    simp only [Matrix.diag_apply,Matrix.mul_apply, RingHom.mapMatrix_apply,Matrix.map_apply]
    exact Legs.sum _ _ fun j _=> Legs.c_mul _ (ordered_legs (G:=G) _ p k j i)
  unfold slotCoeff; rw [neg_mul]; exact Legs.neg (Legs.c_mul _ (Legs.sub (he _) (he _)))

omit [AddCommGroup X] [One X] in
lemma read_ext {p q : Feynman G X} (h : ∀ v, read v p = read v q) : p = q := by
  -- as for Labels.eval_ext: real data are infinite in each physical coordinate
  apply MvPolynomial.funext_set (fun _ => Set.range (fun r : ℝ=> (r:ℂ))) (fun _=>
    Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  choose r hr using fun i => hx i (Set.mem_univ i)
  let v : LogField G X := fun e=> WithLp.toLp 2 (fun i=>r (e,i))
  have he : x = fun i=> (↑(v i.1 i.2):ℂ) := by
    funext i; rcases i with ⟨a,b⟩
    change x (a,b)= (↑(r (a,b)):ℂ); exact (hr _).symm
  rw [he]; exact h v

lemma slot_flat (s : Slot) (c : G.ColorIndex) : slotCoeff G s c 0 = 0 := by
  apply read_ext; intro v
  have he (x : Cover) (s : Walk) : travel (rise v 0) x s = 1 := by
    induction s generalizing x with
    | nil => rfl
    | cons d s ih => rw [travel,ih,Step.read]; split <;> simp [rise]
  rw [slot_jet,_root_.map_zero,Germ.jet_zero,← loop_eval,he]
  simp

-- Homogeneity also in the sense of rescaling physical log inputs (these are real).
omit [AddCommGroup X] [One X] in
lemma legs_scale (v : LogField G X) {p : Feynman G X} {k : ℕ} (hp : legs k p) (z : ℝ) :
    read (z • v) p = read v p * ((z:ℂ)^k) := by
  have hs : read (z • v) = MvPolynomial.eval (fun i=> ((v i.1 i.2:ℝ):ℂ) * (z:ℂ)) := by
    unfold read
    congr 1
    funext i
    simp [mul_comm]
  rw [hs]
  refine Germ.eval_monomialScale _ _ _ k (fun b hb=> ?_)
  simpa only [Finsupp.weight_apply,smul_eq_mul,mul_one] using hp (mem_support_iff.mp hb)

end YM.RG06.WilsonRules
