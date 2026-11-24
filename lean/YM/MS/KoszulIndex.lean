import YM.MS.KoszulAllocate

set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Finset Set
variable {A B R:Type*} [CommRing R] {F G: Raw A R} {v: A→ℤ} {h:ℤ}
def chargeInt (v:A→ℤ)(l:Legs A): ℤ:= (l.map v).sum
@[simp] lemma charge_int {i l}: chargeInt v (i::l)=v i+chargeInt v l:= by simp [chargeInt]
def Rails (v:A→ℤ)(h:ℤ)(F:Raw A R) := ∀ l,chargeInt v l≠h→ F l=0
namespace Rails
lemma smul (c:R)(H:Rails v h F): Rails v h (c • F):=fun l hl=>by simp [H l hl]
lemma sub (H:Rails v h F)(K:Rails v h G): Rails v h (F-G):=fun l hl=> by simp [H l hl,K l hl]
lemma sum {f:B→Raw A R}(s:Finset B)(H:∀ i∈s,Rails v h (f i)): Rails v h (∑ i∈s,f i):= by
    intro l hl; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun i hi=> H i hi l hl
end Rails
end YM.MS.Koszul
