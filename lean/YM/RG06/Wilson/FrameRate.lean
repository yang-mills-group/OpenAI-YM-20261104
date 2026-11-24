import YM.RG06.Wilson.Motif
/-!
# Grading of the path compiler

Homogeneity and exact available link addresses of *each coefficient*.
No linearization in the labels or in the paths. Address collisions are
included by using the same variable for repeated edges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.WilsonCompiler
open GSeries Function Lattice RG
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {V : Type*} {G : Gauge}

/-- Pure ordinary degree in log inputs plus the allowed alphabet. -/
structure Frozen (s : Set V) (k : ℕ) (p : Pigment V) : Prop where
  grade : MvPolynomial.IsWeightedHomogeneous (fun _ => (1:ℕ)) p k
  hits : ∀ x∈p.vars,x∈s
namespace Frozen
open MvPolynomial
variable {s : Set V} {k l : ℕ} {p q : Pigment V}
lemma mono (h : Frozen s k p) {t : Set V} (e : s⊆t) : Frozen t k p :=
  ⟨h.grade, fun x hx=>e (h.hits x hx)⟩
lemma nil (s : Set V) (k : ℕ) : Frozen s k 0 := ⟨ (MvPolynomial.weightedHomogeneousSubmodule ..).zero_mem,by simp⟩
lemma fixed (s : Set V) (c : ℂ) : Frozen s 0 (MvPolynomial.C c) := by
  refine ⟨?_,by simp⟩; simpa using (MvPolynomial.isWeightedHomogeneous_one ℂ (fun _ : V => (1:ℕ))).C_mul c
lemma peg (x : V) (h : x∈s) : Frozen s 1 (MvPolynomial.X x) :=
  ⟨MvPolynomial.isWeightedHomogeneous_X .., fun i hi=> by
    rw [MvPolynomial.vars_X,Finset.mem_singleton] at hi; exact hi ▸ h⟩
lemma add (h : Frozen s k p) (i : Frozen s k q) : Frozen s k (p+q) :=
  ⟨(MvPolynomial.weightedHomogeneousSubmodule ..).add_mem h.grade i.grade,
    fun _x hx=> (Finset.mem_union.mp (MvPolynomial.vars_add_subset p q hx)).elim (h.hits _) (i.hits _)⟩
lemma mul (h : Frozen s k p) (i : Frozen s l q) : Frozen s (k+l) (p*q) :=
  ⟨h.grade.mul i.grade,
    fun _x hx=> (Finset.mem_union.mp (MvPolynomial.vars_mul p q hx)).elim (h.hits _) (i.hits _)⟩
lemma C_mul (h : Frozen s k p) (a : ℂ) : Frozen s k (MvPolynomial.C a * p) := zero_add k ▸ (fixed s a).mul h
lemma neg (h : Frozen s k p) : Frozen s k (-p) := by simpa using h.C_mul (-1)
lemma sub (h : Frozen s k p) (i : Frozen s k q) : Frozen s k (p-q) := by rw [sub_eq_add_neg]; exact h.add i.neg
lemma conj (h : Frozen s k p) : Frozen s k (conjugateP V p) := by
  refine ⟨fun {a} ha=>?_,fun i hi=> h.hits i (MvPolynomial.vars_map p (starRingEnd _) hi)⟩
  apply h.grade; intro he; apply ha; rw [conjugateP, MvPolynomial.coeff_map, he, map_zero]

lemma sum {I : Type*} (t : Finset I) (P : I → Pigment V) (h : ∀ x∈t,Frozen s k (P x)) : Frozen s k (∑ i∈t,P i) := by
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact nil ..
  | insert a t ha ih => rw [Finset.sum_insert ha]; exact (h a (Finset.mem_insert_self ..)).add (ih fun _ hi=>h _ (Finset.mem_insert_of_mem hi))
end Frozen

def Ballroom (s : Set V) (k : ℕ) (Q : Easel G V) := ∀ i j, Frozen s k (Q i j)
namespace Ballroom
variable {s : Set V} {i j : ℕ} {A B : Easel G V}
lemma nil (s : Set V) (G : Gauge) (k : ℕ) : Ballroom s k (0:Easel G V) := fun _ _=> Frozen.nil ..
lemma one (s : Set V) (G : Gauge) : Ballroom s 0 (1:Easel G V) := by
  intro i j; rcases eq_or_ne i j with e|e
  · subst j; rw [Matrix.one_apply_eq]; simpa using Frozen.fixed s 1
  rw [Matrix.one_apply_ne e]; exact Frozen.nil ..
lemma mul (h : Ballroom s i A) (e : Ballroom s j B) : Ballroom s (i+j) (A*B) := by
  intro k l; rw [Matrix.mul_apply]; exact Frozen.sum _ _ fun x _=>(h k x).mul (e x l)
lemma neg (h : Ballroom s i A) : Ballroom s i (-A) := fun x y=> (h x y).neg
lemma scalar (h : Ballroom s i A) (a : ℂ) : Ballroom s i (MvPolynomial.C (σ:=V) a • A) := fun x y=> (h x y).C_mul a
lemma sum {I : Type*} (t : Finset I) (P : I → Easel G V) (h : ∀ x∈t,Ballroom s i (P x)) : Ballroom s i (∑ k∈t,P k) := by
  intro x y; rw [Matrix.sum_apply]; exact Frozen.sum _ _ fun z he=>h z he x y

lemma color (s : Set V) (x : G.ColorIndex→V) (h : ∀ i,x i ∈ s) : Ballroom s 1 (colorTube G fun i=> MvPolynomial.X (x i)) := by
  intro i j; unfold colorTube; rw [Matrix.of_apply]; apply Frozen.sum; intro k _; exact (Frozen.peg (x k) (h k)).mul (Frozen.fixed s _)
end Ballroom

-- lift grading to two kinds of power series

def Monorail (s : Set V) (m : Animation G V) := ∀ k, Ballroom s k (PowerSeries.coeff k m)
def Trellis (s : Set V) (p : PowerSeries (Pigment V)) := ∀ k, Frozen s k (PowerSeries.coeff k p)
namespace Monorail
variable {s : Set V} {m p : Animation G V}
lemma solo (s : Set V) (G : Gauge) : Monorail s (1:Animation G V) := by
  intro k; cases k <;> rw [PowerSeries.coeff_one]
  · simpa using Ballroom.one s G
  simp only [Nat.add_one_ne_zero, ↓reduceIte]; exact Ballroom.nil _ _ _
lemma join (h : Monorail s m) (e : Monorail s p) : Monorail s (m*p) := by
  intro k; rw [PowerSeries.coeff_mul]; refine Ballroom.sum _ _ fun x hK=>?_
  have hw:= Finset.mem_antidiagonal.mp hK
  exact hw ▸ Ballroom.mul (h x.1) (e x.2)
lemma running {A : Easel G V} (h : Ballroom s 1 A) : Monorail s (logRoll A) := by
  intro k; rw [logRoll,PowerSeries.coeff_mk]; apply Ballroom.scalar
  induction k with
  | zero=> exact pow_zero A ▸ Ballroom.one s _
  | succ k ih=> rw [pow_succ]; exact Ballroom.mul ih h
end Monorail
namespace Trellis
variable {s : Set V} {a b : PowerSeries (Pigment V)}
lemma still (s : Set V) (a : ℂ) : Trellis s (tray a) := by
  intro k; cases k <;> rw [PowerSeries.coeff_C]
  · simp only [↓reduceIte]; exact Frozen.fixed ..
  simp only [Nat.add_one_ne_zero, ↓reduceIte]; exact Frozen.nil ..
lemma nil (s : Set V) : Trellis s 0 := by simpa [tray] using still s 0
lemma mono (h : Trellis s a) {t : Set V} (e : s⊆t) : Trellis t a := fun k=> Frozen.mono (h k) e
lemma add (h : Trellis s a) (e : Trellis s b) : Trellis s (a+b) := fun k=> by rw [map_add]; exact (h k).add (e k)
lemma sub (h : Trellis s a) (e : Trellis s b) : Trellis s (a-b) := fun k=> by rw [map_sub]; exact (h k).sub (e k)
lemma mul (h : Trellis s a) (e : Trellis s b) : Trellis s (a*b) := by
  intro k; rw [PowerSeries.coeff_mul]; refine Frozen.sum _ _ fun x hx=>?_; exact (Finset.mem_antidiagonal.mp hx) ▸ ((h x.1).mul (e x.2))
lemma sum {I : Type*} {l : Finset I} (P : I→ PowerSeries (Pigment V)) (h : ∀ i∈l,Trellis s (P i)) : Trellis s (∑ i∈l,P i) := by
  intro k; rw [map_sum]; exact Frozen.sum _ _ fun i hi=>h i hi k
lemma frame {p : Animation G V} (h : Monorail s p) (i j : Fin G.repDim) (b : Bool) : Trellis s (frameP p i j b) := by
  intro k; rw [frameP, PowerSeries.coeff_mk]; split
  · exact (h k i j).conj
  exact h k i j
lemma extracted {p : Animation G V} (h : Monorail s p) (L : G.Mat →ₗ[ℝ] ℂ) : Trellis s (extract L p) := by
  unfold extract; apply sum; intro i _; apply sum; intro j _; apply Trellis.add
  · exact (( (still s _).mul ((frame h _ _ _).add (frame h _ _ _))).mul (still s _))
  exact (((still s _).mul ((frame h _ _ _).sub (frame h _ _ _))).mul (still s _))
lemma compiler {I : Type*} (p : MvPolynomial I ℂ) (v : I→PowerSeries (Pigment V)) (h : ∀ i,Trellis s (v i)) : Trellis s (compile v p) := by
  induction p using MvPolynomial.induction_on with
  | C c=> rw [compile,MvPolynomial.eval₂Hom_C]; exact still s c
  | add p q hp hq=> rw [map_add]; exact hp.add hq
  | mul_X p i hp=> rw [map_mul]; apply Trellis.mul hp; rw [compile,MvPolynomial.eval₂Hom_X']; exact h i
end Trellis

section
variable {D : Type*} [AddCommGroup D] [One D] {s : Set V}
variable (K : display G D V)

theorem step_pay (x : Four D) (d : Step) (h : Ballroom s 1 (K (d.used x))) : Monorail s (stepSeq K x d) := by
  unfold stepSeq; cases he:d.neg <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact Monorail.running h
  exact Monorail.running (Ballroom.neg h)

def fieldTrip (x : Four D) : Walk → List (DLink D)
 | []=> []
 | d::w=> d.used x::fieldTrip (x+d.vec) w

-- every link in compiler polynomial is covered by the edge path, bound repeated
-- length for analytic budgets though support only charged once
@[simp] lemma fieldTrip_length (x : Four D) (w : Walk) : (fieldTrip x w).length=w.length := by
  induction w generalizing x with
  | nil => rfl
  | cons d s ih=> simp only [fieldTrip,List.length_cons,ih]

theorem shooting_range (x : Four D) (w : Walk) (h : ∀ e ∈ fieldTrip x w,Ballroom s 1 (K e)) : Monorail s (shoot K x w) := by
  induction w generalizing x with
  | nil => exact Monorail.solo _ _
  | cons d w ih =>
    exact Monorail.join (step_pay K x d (h _ List.mem_cons_self)) (ih _ fun l hl=>h _ (List.mem_cons_of_mem _ hl))

def pathBudget (G : Gauge) (x : Four D) (w : Walk) : Set (LinkVar G D) := fun i=> i.1 ∈ fieldTrip x w

theorem path_pure (G : Gauge) (x : Four D) (w : Walk) :
    Monorail (pathBudget G x w) (shoot (basic G D) x w) := by
  apply shooting_range
  intro e h; exact Ballroom.color _ (fun i=> (e,i)) (fun _=> h)

theorem slot_pure (G : Gauge) (x : Four D) (b : Slot) (i : G.ColorIndex) : Trellis
    (pathBudget G x (Work.F02.slotWalk b)) (slotSeq (basic G D) x b i) :=
  Trellis.extracted (path_pure G x _) _

open Source

omit [AddCommGroup D] [One D] in
theorem film_pure {S : Finset Cover} (p : Formula G S) (f : UsedEdges S → DLink D)
    (h : ∀ i: UsedEdges S, Ballroom s 1 (K (f i))) :
    Trellis s (film p K f) := Trellis.compiler p _ fun i=> Trellis.frame (Monorail.running (h i.1)) i.2.1 i.2.2.1 i.2.2.2

def eats (G : Gauge) (S : Set (Four D)) : Set (LinkVar G D) := fun i=> i.1.1∈S ∧ i.1.1+step i.1.2∈S

theorem request_cover (C : Family G) (d : ℕ) (x : C.label d) :
    Trellis (eats G (C.localSection d).stencil) (markTop C d x) :=
  film_pure (basic G ℤ) _ _ fun i=> Ballroom.color _ _ (fun _=> i.property)

theorem request_site {n : Side} (C : Family G) (d : ℕ) (x : C.label d) (o : Site n) :
    Trellis (eats G ((C.localSection d).footprint o)) (markSite C d x o):= by
  apply film_pure
  intro i
  refine Ballroom.color _ (fun j=> (place o i,j)) ?_
  intro j
  constructor
  · exact Finset.mem_image_of_mem _ i.property.1
  · refine Finset.mem_image.mpr ⟨i.val.1+step i.val.2,i.property.2,?_⟩
    change wrap n _ + _ = _ + _ + step _
    rw [map_add,wrap_step]; change _ = _ + o + step i.val.2; abel
end
end YM.RG06.WilsonCompiler
