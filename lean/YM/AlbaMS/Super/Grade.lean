import YM.AlbaMS.Super.Thrill
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
graded double derivative and backwards sign. Use for even Cov and odd
BV second-order operation, with scalars including pairing-volume factors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι R U : Type*} [CommRing R] {ρ : ι→Bool} (p q e : Bool) (x y : ι)
variable (F G H : Coil ρ R) {l : List ι} (n : ℕ)
lemma sting_sum {E : Type*} [AddCommGroup E] (s : Finset U)(f : U→ E) : sting p (∑ i ∈ s, f i)=∑ i∈s,sting p (f i):=by cases p <;> simp [Finset.sum_neg_distrib]

namespace Coil
lemma plane_twice : plane p (plane q F)=plane (xor p q) F:=by
  ext l; simp only [polar]; cases p<;>cases q<;>cases band ρ l<;>simp

def touch (k : ι→ι→R)(s : Finset ι) : Coil ρ R→ₗ[R] Coil ρ R := ∑ i∈s, ∑ j∈s,k i j • ((D j).comp (D i))
variable (k k' : ι→ι→R) (s t : Finset ι)
def Graded (ρ : ι→ Bool) (p : Bool)(k : ι→ι→R):Prop:= ∀ i j,k i j≠0→xor (ρ i) (ρ j)=p
lemma touch_apply : touch k s F=∑ i∈s,∑ j∈s,k i j • (D j (D i F)):=by simp_rw [touch,LinearMap.sum_apply, LinearMap.smul_apply,LinearMap.comp_apply]
lemma touch_sting : touch k s (sting p F)=sting p (touch k s F):=by cases p <;> simp
lemma touch_const (c:R): touch k s (put ρ c)=0:=by simp [touch_apply]
lemma touch_one : touch k s (1:Coil ρ R)=0:=touch_const ..
lemma touch_tone (h:Tone e F)(H:Graded ρ p k): Tone (xor e p) (touch k s F):=by
  rw [touch_apply]; refine Tone.sum _ _ (fun i _=> Tone.sum _ _ fun j _=> ?_)
  by_cases he:k i j=0
  · rw [he,zero_smul]; apply Tone.none
  rw [← H i j he,← Bool.xor_assoc]; exact ((h.dz i).dz j).smul _
lemma D_touch (h:Graded ρ p k): D x (touch k s F)=sting (ρ x && p) (touch k s (D x F)):=by
  rw [touch_apply,touch_apply]; simp_rw [map_sum,map_smul,sting_sum,sting_smul]
  refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_
  by_cases he:k i j=0
  · simp [he]
  rw [DD (D i F),DD F,D_sting,←h i j he]; cases ρ i<;> cases ρ j<;>cases ρ x<;> simp
lemma touch_touch (h:Graded ρ p k)(H: Graded ρ q k'): touch k s (touch k' t F)=sting (p && q) (touch k' t (touch k s F)):=by
  rw [touch_apply, touch_apply F k s]; simp_rw [map_sum,map_smul,sting_sum,sting_smul]
  refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_
  by_cases he:k i j=0
  · simp [he]
  rw [D_touch _ _ _ _ _ H,D_sting,D_touch _ _ _ _ _ H,← h i j he]; cases ρ i<;>cases ρ j<;> cases q<;> simp
lemma Cap.touch (h:Cap F (n+2)): Cap (Coil.touch k s F) n:=touch_apply F k s ▸ Cap.sum _ _ fun i _=> Cap.sum _ _ fun j _=>Cap.smul ((h.dz i).dz j) _
lemma Heg.touch (h:Heg (n+2) F): Heg n (Coil.touch k s F):=touch_apply F k s ▸ Heg.sum _ _ fun i _=> Heg.sum _ _ fun j _=> Heg.smul ((h.D_zone i).D_zone j) _
lemma Inside.touch {u}(h:Inside u F): Inside u (Coil.touch k s F):=touch_apply F k s ▸ Inside.sum _ _ fun i _=>Inside.sum _ _ fun j _=> Inside.smul ((h.dz i).dz j) _
lemma touches (h:Inside (s:Set ι) F)(H:s⊆t): touch k s F=touch k t F:=by
  rw [touch_apply,touch_apply]; apply (Finset.sum_congr (s₂:=s) (g:=fun i=> ∑ j∈t,k i j • (D j (D i F))) rfl ?_).trans (Finset.sum_subset H ?_)
  · intro i hi; refine Finset.sum_subset H fun j _ hj=> ?_; rw [(h.dz i).erased hj,smul_zero]
  intro i _ hi; rw [h.erased hi]; simp
lemma touched (h:Cap F 1) : touch k s F=0:=by rw [touch_apply]; apply Finset.sum_eq_zero; intro i _; conv=> lhs; rw [(h.dz i).eroded]; simp
lemma add_touch : touch (k+k') s F=touch k s F+touch k' s F:=by simp_rw [touch_apply,Pi.add_apply,add_smul,Finset.sum_add_distrib]
lemma pay_touch (c:R): touch (c • k) s F=c • touch k s F:= by simp_rw [touch_apply,Pi.smul_apply,smul_eq_mul,← smul_smul, Finset.smul_sum]

-- Cross: robust with arbitrary even or odd operands, recovers actual bracket by (+/-) factor
-- both inputs even (no costs on mark sources) gives raw. explicit Slot form.
def link (ρ : ι→Bool)(x y:ι)(F G : Coil ρ R): Coil ρ R := plane (ρ y) (D x F)* D y G + D y (plane (ρ x) F)*D x G
lemma gear : D y (D x (F*G))=D y (D x F)*G + plane (xor (ρ x) (ρ y)) F * D y (D x G)+link ρ x y F G:=by
  simp only [mulD,map_add,link,plane_twice, Bool.xor_comm (ρ y)]; abel

def cross (d : Bool)(k : ι→ι→R)(s : Finset ι) (F G : Coil ρ R) := touch k s (F*G) - touch k s F*G - plane d F * touch k s G
lemma from_cross (h:Graded ρ p k): cross p k s F G=∑ i∈s,∑ j∈s,k i j • link ρ i j F G:=by
  unfold cross; simp_rw [touch_apply, Finset.sum_mul, Finset.mul_sum,mul_smul_comm,smul_mul_assoc,← Finset.sum_sub_distrib,← smul_sub]; -- mul smul wrong?
  refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_
  by_cases he:k i j=0
  · simp [he]
  rw [gear,h i j he]; congr 1; abel
lemma tone_cross {e d : Bool} (ht:Tone e F)(h:Tone d G)(hk:Graded ρ p k): Tone (xor e (xor d p)) (cross p k s F G):=by
  have he : Tone (xor d p) (touch k s G):= touch_tone _ _ _ _ _ h hk -- fix
  have ha : Tone (xor e (xor d p)) (touch k s (F*G)):= by rw [← Bool.xor_assoc]; exact touch_tone _ _ _ _ _ (ht.mul h) hk
  refine (ha.sub ?_).sub ?_; rw [show xor e (xor d p)=xor (xor e p) d by cases p<;>cases d<;>cases e<;>rfl]; exact (touch_tone _ _ _ _ _ ht hk).mul h; rw [ht.pl]; exact (ht.stingIt _).mul he
end Coil
end YM.MSBar.Bric
