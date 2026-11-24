import YM.MS.KoszulEdges
import Mathlib.Tactic.LinearCombination

/-! Separated identities for a master equation test — proven from graded operations.
Using symmetry explicitly (two loop interchange needs it); the connected read afterwards cannot
use this proof relying on global zero-frequency values. Instead approximate multilinear identities. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Set Finset
variable {R A I J : Type*} [CommRing R] {p : Sector A} {u v f g : Raw A R}
local infixl:70 " ⋄ " => product p
variable {b c : Bool}

-- summing a specified finite row
def loop (r : I→R) (a e : I→A) (s : Finset I) : Op A R := ∑ i∈s, r i • diffPair (a i) (e i)

/-- retain all symmetry and zero support -/
def Balanced (p : Sector A) (b : Bool) (r : I→R) (a e : I→A) (s : Finset I) := ∀ i∈ s, r i≠0→ (p (e i) ^^ p (a i))= b
lemma Balanced.pure {d : Bool} {r : I→R} {a e s} (h: Balanced p b r a e s) (hf : Pure p d f) : Pure p (d ^^ b) (loop r a e s f):= by
   simp only [loop, LinearMap.sum_apply,LinearMap.smul_apply,diffPair_apply]; apply Pure.sum; intro i hi
   by_cases ht:r i=0
   · simpa only [ht,zero_smul] using Pure.zero (p:=p) (b:=d^^b) (R:=R)
   rw [← h i hi ht, Bool.xor_comm (p (e i)), ← Bool.xor_assoc]; exact ((hf.drop _).drop _).smul _
lemma loop_symm {r : I→R} {a e s} (hf : Symm p f) : Symm p (loop r a e s f) := by
   simp only [loop, LinearMap.sum_apply,LinearMap.smul_apply,diffPair_apply]; exact Symm.sum _ (fun i _=> ((hf.drop (a i)).drop _).smul _)
lemma loop_loop {d : Bool} {P:I→ R} {L : J → R} {a e s a' e' s'}
    (hP:Balanced p b P a e s) (hL:Balanced p d L a' e' s') (hf: Symm p f) :
    loop P a e s (loop L a' e' s' f) = (cross b d:R) • loop L a' e' s' (loop P a e s f) := by
   simp only [loop, LinearMap.sum_apply, LinearMap.smul_apply,map_sum,map_smul, Finset.smul_sum]
   rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj
   by_cases h : P i=0; simp [h]; by_cases H:L j=0; simp [H]
   rw [exchange2 (a i) (e i) (a' j) (e' j) hf, Bool.xor_comm (p (a i)),hP _ hi h, Bool.xor_comm (p (a' j)), hL _ hj H]
   simp only [smul_smul]; ring_nf
private lemma square_identity (K : Op A R) (b : Bool) (h : Pure p false f) :
    K (f ⋄ f)=link K b p f f+(2:ℕ) • (f ⋄ K f) := by
     nth_rw 1 [link_even (v:=f) (b:=b) K h]; rw [← h.central]; abel
-- quadratic identities
lemma master_quad {X : Shift R p true} {P L : Op A R} (f: Raw A R) (hf : Symm p f) (he : Pure p false f)
    (Pe : Pure p false (P f))
    (h : ∀ z, Symm p z → X.Q (P z) + L z=P (X.Q z)) :
    X.Q (link P false p f f)+link L true p f f=(2:ℕ) • link P false p f (X.Q f) := by
   have hS := h (f ⋄ f) (hf.times hf); have H : P (X.Q f)= X.Q (P f)+L f:=(h f hf).symm
   rw [square_identity P false he, square_identity L true he,X.product_rule _ _, ← he.central (X.Q f), he.signs] at hS
   simp only [cross_false',one_smul] at hS
   rw [← two_nsmul, map_nsmul, link_apply P f (X.Q f) (b:=false),sign_id,H] at hS
   simp only [X.product_rule,he.signs,map_add, map_nsmul] at hS
   -- cross terms (Q f)*Pf vs Pf *Qf: need P even.
   rw [Pe.central] at hS; simp only [one_smul,cross_false', nsmul_add] at hS; linear_combination (norm:=abel) hS

variable {r : I→R} {a e s} (h : Balanced p b r a e s)
include h
lemma Balanced.paired (ha:Pure p false f) (hu:Pure p false u) :
   link (loop r a e s) b p f (u ⋄ v) = link (loop r a e s) b p f u ⋄ v+ u ⋄ (link (loop r a e s) b p f v) := by
   simp only [loop, link_sum, link_scale,map_sum, LinearMap.sum_apply,map_smul, LinearMap.smul_apply, ← sum_add_distrib]; apply sum_congr rfl; intro i hi; by_cases hz:r i=0; simp [hz]; rw [pair_products (a i) (e i) (h i hi hz) ha hu,smul_add]
omit h in
lemma pair_products_left (i j : A) (h: (p j ^^ p i)=b) (ha:Pure p false f) (hu:Pure p false u) :
   link (diffPair i j) b p (u ⋄ f) v = u ⋄ link (diffPair i j) b p f v + f ⋄ (link (diffPair i j) b p u v) := by
   rw [link_pair_left i j h v (hu.prod ha),link_pair_left i j h v ha,link_pair_left i j h v hu]
   simp only [D_product,map_add, hu.signs,cross_false',one_smul];
   rw [← ha.central,← ha.central]; simp only [times_assoc, LinearMap.add_apply,smul_add,map_smul] -- use simp order
   abel
-- accidentally h ambient `include h`
lemma Balanced.paired_left (ha:Pure p false f) (hu:Pure p false u) :
   link (loop r a e s) b p (u ⋄ f) v = u ⋄ link (loop r a e s) b p f v+ f ⋄ (link (loop r a e s) b p u v) := by
   simp only [loop, link_sum, link_scale,map_sum, ← sum_add_distrib]; apply sum_congr rfl; intro i hi; by_cases hz:r i=0; simp [hz]; rw [pair_products_left (a i) (e i) (h i hi hz) ha hu,smul_add,map_smul,map_smul]
lemma cube_rule (ha: Pure p false f) :
    (loop r a e s) (f ⋄ (f ⋄ f)) = (3:ℕ) • (f ⋄ (link (loop r a e s) b p f f)) + (3:ℕ) • ((f ⋄ f) ⋄ (loop r a e s f)) := by
    let K:=loop r a e s
    change K _ = (3:ℕ) • (f ⋄ link K b p f f) + (3:ℕ) • ((f ⋄ f) ⋄ K f)
    nth_rw 1 [link_even (b:=b) K ha, show link K b p f (f ⋄ f) = _ from h.paired ha ha, square_identity K b ha]
    simp only [map_add,map_nsmul]
    rw [← (ha.prod ha).central (K f),← ha.central (link (loop r a e s) b p f f)];
    dsimp only [K]; simp only [← times_assoc]; abel
omit h
lemma quad_loop {T P:Op A R} {d : Bool} (he:Pure p false f) (hs: Symm p f)
    (ha : Pure p false (P f))
    (h : ∀ g, Symm p g → T (P g)= P (T g)) :
    T (link P false p f f)+(2:ℕ) • link T d p f (P f) =
    P (link T d p f f)+(2:ℕ) • link P false p f (T f) := by
    have H := h (f ⋄ f) (hs.times hs); rw [square_identity P false he,square_identity T d he] at H
    simp only [map_add,map_nsmul] at H; rw [link_even P he (v:=T f) (b:=false),link_even (b:=d) T he (v:=P f),ha.central,h f hs] at H
    linear_combination (norm:=abel) H

include h
lemma cubic_loop {P:J → R} {u w t} -- fix
    (H : Balanced p false P u w t) (hs: Symm p f) (he:Pure p false f) :
   let T:=loop r a e s; let B:=loop P u w t;
   (3:ℕ) • link T b p f (link B false p f f)=(3:ℕ) • link B false p f (link T b p f f) := by
   intro T B
   have hL (x :Raw A R) (hg : Symm p x) : T (B x)=B (T x):= by unfold T B; simpa using loop_loop h H hg
   have hu : Pure p false (B f) := H.pure he
   have hx : Pure p false (link B false p f f):= link_pure B (fun _ _ H'=> H.pure H') he he -- adjust
   have hh := quad_loop (d:=b) (T:=T) he hs hu hL
   replace hh := congr_arg (fun x=> f ⋄ x) hh
   have hz:= hL (f ⋄ (f ⋄ f)) (hs.times (hs.times hs)); rw [show B (f ⋄ _) = _ from cube_rule H he, show T (f ⋄ _) = _ from cube_rule h he] at hz
   change T ((3:ℕ) • (f ⋄ link B false p f f) + (3:ℕ) • ((f ⋄ f) ⋄ B f)) = B ((3:ℕ) • (f ⋄ link T b p f f) + (3:ℕ) • ((f ⋄ f) ⋄ T f)) at hz
   simp only [map_add,map_nsmul] at hh hz
   rw [link_even T he (b:=b) (v:=link B false p f f), link_even B he (b:=false) (v:=link T b p f f), link_even T (he.prod he) (b:=b) (v:=B f),link_even B (he.prod he) (b:=false) (v:=T f)] at hz
   rw [show link T b p (f ⋄ f) (B f)= f ⋄ _+f ⋄ _ from h.paired_left he he, show link B false p (f ⋄ f) (T f)=f ⋄ _+f ⋄ _ from H.paired_left he he, square_identity B false he, square_identity T b he,hL f hs] at hz
   simp only [map_add,map_nsmul,LinearMap.add_apply, LinearMap.smul_apply, times_assoc] at hz
   rw [hx.central,hu.central (link T b p f f),hu.central (T f)] at hz
   dsimp only [T,B] at *; linear_combination (norm:=abel) hz - hh - hh - hh
end YM.MS.Koszul
