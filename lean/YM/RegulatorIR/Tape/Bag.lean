import YM.RegulatorIR.Tape.Product

/-! Sums over incidences (not over distinct values). -/
noncomputable section
namespace YM.RegulatorIR
open Function Set Filter
open scoped NNReal ENNReal BigOperators Classical
variable {α β γ σ τ : Type*}

section plain
variable {X : Type*} [AddCommMonoid X]
/-- Sum over slots with multiplicities. -/
def bag (s : Multiset α) (f : α → X) := (s.map f).sum
lemma bag_congr {s : Multiset α} {f g : α → X} (h : ∀ x ∈ s, f x = g x) : bag s f = bag s g := by unfold bag; rw [Multiset.map_congr rfl h]
@[simp] lemma bag_empty (f : α → X) : bag 0 f = 0 := rfl
@[simp] lemma bag_cons (s : Multiset α) (f : α → X) (x : α) : bag (x ::ₘ s) f = f x + bag s f := by simp [bag]
@[simp] lemma bag_singleton (x : α) (f : α → X) : bag {x} f = f x := by simp [bag]
lemma bag_plus (s t : Multiset α) (f : α → X) : bag (s+t) f = bag s f + bag t f := by simp [bag]
lemma bag_add (s : Multiset α) (f g : α → X) : bag s (fun i => f i + g i) = bag s f + bag s g := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [ih]; abel
lemma bag_const (s : Multiset α) (x : X) : bag s (fun _ => x) = s.card • x := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [ih,add_nsmul,add_comm]
@[simp] lemma bag_zero (s : Multiset α) : bag s (fun _ => (0:X)) = 0 := by rw [bag_const]; simp
lemma bag_map (s : Multiset α) (f : α → β) (g : β → X) : bag (s.map f) g = bag s (g ∘ f) := by unfold bag; rw [Multiset.map_map]
lemma bag_comm (s : Multiset α) (t : Multiset β) (f : α → β → X) : bag s (fun i => bag t (f i)) = bag t (fun j => bag s (fun i => f i j)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih => simp_rw [bag_cons,ih]; exact (bag_add ..).symm
lemma hom_bag {Y : Type*} [AddCommMonoid Y] (g : X →+ Y) (s : Multiset α) (f : α → X) :
    g (bag s f) = bag s (fun x => g (f x)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp only [bag_cons,map_add, ih]
lemma bag_finset (s : Multiset α) (t : Finset β) (k : α → β → X) :
    bag s (fun i => ∑ j∈t,k i j) = ∑ j∈t,bag s (fun i => k i j) := bag_comm _ t.val k
lemma bag_apply (s : Multiset α) (F : α → β → X) (x : β) : bag s F x = bag s (fun i => F i x) := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons _ _ ih => simp [ih]
lemma bag_le [Preorder X] [AddLeftMono X] {s : Multiset α} {f g : α → X} (h : ∀ i∈s, f i ≤ g i) : bag s f ≤ bag s g := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp only [bag_cons]; exact add_le_add (h _ (by simp)) (ih (fun i hi => h i (by simp [hi])))
lemma bag_erase [DecidableEq α] (s : Multiset α) (f : α → X) {i : α} (hi : i ∈ s) :
    f i + bag (s.erase i) f = bag s f := by rw [← bag_cons,Multiset.cons_erase hi]
end plain
lemma bag_smul {X : Type*} [AddCommMonoid X] [DistribSMul ℝ X] (a : ℝ) (s : Multiset α) (f : α → X) :
    a • bag s f = bag s (fun x => a • f x) := hom_bag (DistribSMul.toAddMonoidHom X a) ..
namespace Tape
lemma tally_bag (w : Weight α) (s : Multiset β) (F : β → Tape α) : tally w (bag s F) ≤ bag s (fun i => tally w (F i)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih => rw [bag_cons,bag_cons]; exact (tally_add ..).trans (add_le_add le_rfl ih)
lemma Carried.bag {F : β → Tape α} {w : Weight α} {s : Multiset β} (h : ∀ i∈s, Carried (F i) w) : Carried (bag s F) w := by
  induction s using Multiset.induction_on with
  | empty => simp [Carried]
  | cons i s ih => rw [_root_.YM.RegulatorIR.bag_cons]; exact (h _ (by simp)).add (ih (fun i hi => h i (by simp [hi])))
lemma Within.bag {F : β → Tape α} {S : Set α} {s : Multiset β} (h : ∀ i∈s, Within S (F i)) : Within S (bag s F) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih => rw [bag_cons]; exact (h _ (by simp)).add (ih (fun i hi => h i (by simp [hi])))
lemma bag_mix {F : γ → Tape α} {s : Multiset γ} {S : Set α} {w : Weight α} {v : Weight β}
    {k : Rows α β} {C : ℝ≥0∞} (hf : ∀ i∈s, Within S (F i))
    (h : Meter S w v C k) (hC : C < ∞) (hv : Lower v) (hF : ∀ i∈s, Carried (F i) w) :
    mix (bag s F) k = bag s (fun i => mix (F i) k) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
    rw [bag_cons,bag_cons,add_mix (hf i (by simp)) (Within.bag (s:=s) (fun j hj => hf j (by simp [hj]))) h hC hv
        (hF i (by simp)) (Carried.bag (fun j hj => hF j (by simp [hj]))), ih (fun j hj => hf j (by simp [hj])) (fun j hj => hF j (by simp [hj]))]
end Tape
end YM.RegulatorIR
