import YM.FormalOPE.RG10.Transit.Books

/-! # Complete moment through a time slab and first-join correction pieces

An `isotropy` or measure proposition isn't used here. Keep the **operators** incurred before any
cluster projection or any exterior choices. Members of the subring here are gauge germs through
the stipulated Taylor order, still on cover stencils with addresses in the inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit.Weave
open Route PowerSeries Finset Function
open scoped Topology BigOperators Classical
variable {U J : ℕ → Type} [∀ i, Fintype (J i)] {I : Type*}
    (V : Voyage U J)
open Voyage Flock
variable {j k N : ℕ}
    (v : Finset I) (P : I → Channel (U N))

def letter (k : ℕ) (a : I) := V.yield k N (P a)
def solo (k : ℕ) := ∏ x∈v,letter V P k x
def all (k : ℕ) := V.yield k N (∏ x∈v,P x)
def expense (j : ℕ) := Flock.leakage V j v (letter V P (j+1))

lemma singling (h : j < N) (a : I): (V.sail j).floats (letter V P (j+1) a)= letter V P j a:=V.approach h _
lemma payment (h : j < N) : (V.sail j).floats (solo V v P (j+1))= solo V v P j+expense V v P j := by
  unfold solo expense Flock.leakage; simp_rw [singling V P h]; ring
lemma inside (hi:k ≤ j) (h:j ≤ N) :
    V.yield k j (solo V v P j) = solo V v P k + ∑ x∈Ico k j,V.yield k x (expense V v P x) := by
  induction j,hi using Nat.le_induction with
  | base=>simp
  | succ j H ih => rw [send_next V H,payment V v P h,map_add, ih (by omega),sum_Ico_succ_top H]; ring
lemma founded (h:k ≤ N) : all V v P k=solo V v P k+∑ i∈Ico k N,V.yield k i (expense V v P i) := by
  rw [← inside V v P h (le_refl _)]; simp only [solo,letter,sameHere]; rfl

variable (F : ∀ i, Subring (Channel (U i)))
structure Sane (V : Voyage U J) (k N : ℕ) (F : ∀ i, Subring (Channel (U i))) (v : Finset I)
    (P : I→Channel (U N)) (r : ℕ) (Z : I→ℕ) : Prop where
  valid : V.authentic F k N
  certify : V.Eligible r k N
  approved x (h:x∈v) : P x∈F N
  rank x (h:x∈v) : Guard (P x) r (Z x)
variable {F V P v} {D : I→ℕ} {r h : ℕ} {t a : ℕ}
    (u : Sane V k N F v P r D)

include u
lemma Sane.law (h : j∈Icc k N) (x : I) (hx : x∈v) : letter V P j x ∈ F j := keeping (u.valid.clip (mem_Icc.mp h).1 le_rfl) (u.approved x hx) (mem_Icc.mp h).2
lemma Sane.born (h : j∈Icc k N) (x : I) (hx : x∈v) : Guard (letter V P j x) r (D x) := positions (u.certify.clip (mem_Icc.mp h).1 le_rfl) (u.rank x hx) (mem_Icc.mp h).2
lemma Sane.rest (h:j∈Icc k N) : solo V v P j∈ F j := (F _).prod_mem (fun i hi => u.law h i hi)
lemma Sane.rank_v (h:j∈Icc k N) : Guard (solo V v P j) r (∑ i∈v,D i):= Guard.prod _ _ _ (u.born h)
lemma Sane.remainder (h : j∈Ico k N) : expense V v P j∈F j := by
  have hj : j∈Icc k N := Ico_subset_Icc_self h
  have hh : j+1∈Icc k N:=mem_Icc.mpr ⟨(mem_Icc.mp hj).1.trans (Nat.le_succ _),(mem_Ico.mp h).2⟩
  unfold expense Flock.leakage; simp_rw [singling V P (mem_Ico.mp h).2]; exact (F _).sub_mem (u.valid j h _ (u.rest hh)) (u.rest hj)
lemma Sane.record (h : j∈Ico k N) : Guard (expense V v P j) r (∑ i∈v,D i) := by
  have hj : j∈Icc k N := Ico_subset_Icc_self h
  have hh : j+1∈Icc k N:=mem_Icc.mpr ⟨(mem_Icc.mp hj).1.trans (Nat.le_succ _),(mem_Ico.mp h).2⟩
  unfold expense Flock.leakage; simp_rw [singling V P (mem_Ico.mp h).2]; exact Guard.sub (Episode.Eligible.forward _ _ _ (u.certify j h) (u.rank_v hh)) (u.rank_v hj)
lemma Sane.sent (h : j∈ Icc k N) : all V v P j∈ F j := keeping (u.valid.clip (mem_Icc.mp h).1 le_rfl) ((F _).prod_mem u.approved) (mem_Icc.mp h).2
lemma Sane.full (h : j∈ Icc k N) : Guard (all V v P j) r (∑ i∈v,D i) := positions (u.certify.clip (mem_Icc.mp h).1 le_rfl) (Guard.prod _ _ _ u.rank) (mem_Icc.mp h).2
end YM.FormalOPE.RG10.Transit.Weave
