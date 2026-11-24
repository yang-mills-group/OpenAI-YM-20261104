import YM.MS.KoszulShift

/-!
# Abstract finite pairwise Wick operation

`diffPair` is ∂_H on the shuffle series. `link` is its polarization cross
acting between two series. We use arbitrary ordered rows as well as parity-
constrained and exchange-equivariant specializations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Set Finset
variable {R A I : Type*} [CommRing R] {p : Sector A} {u v f g : Raw A R}
local infixl:70 " ⋄ " => product p
abbrev Op (A R : Type*) [CommRing R] := Raw A R →ₗ[R] Raw A R
def diffPair (i j : A) : Op A R := (D j).comp (D i)
variable {b c : Bool}

def link (K : Op A R) (b : Bool) (p : Sector A) (f g: Raw A R) := K (product p f g) - product p (K f) g - product p (sign p b f) (K g)
lemma link_apply (K : Op A R) (u v : Raw A R) : K (u ⋄ v) = link K b p u v + (K u) ⋄ v + (sign p b u) ⋄ K v := by unfold link; abel
lemma link_even (K : Op A R) (h : Pure p false u) : K (u ⋄ v) = link K b p u v + (K u) ⋄ v + u ⋄ K v:= by
    nth_rw 1 [link_apply (b:=b)]; rw [h.signs,cross_false',one_smul]
lemma link_pure (K : Op A R) (h : ∀ c F, Pure p c F→ Pure p (c.xor b) (K F)) (hu : Pure p c u) {d : Bool} (hv : Pure p d v) :
    Pure p ((c.xor d).xor b) (link K b p u v) := by
    have hx:= h (c.xor d) _ (hu.prod hv); have hy := (h c _ hu).prod hv; have hz := ((hu.smul (R:=R) (cross b c)).prod (h _ _ hv))
    unfold link; rw [hu.signs]; intro l he; simp only [Pi.sub_apply, hx l he, hy l (show degree p l ≠ (c ^^ b ^^ d) from by rw [Bool.xor_assoc, Bool.xor_comm b d,← Bool.xor_assoc]; exact he), hz l (show degree p l ≠ (c ^^ (d ^^ b)) from by rwa [← Bool.xor_assoc]),sub_self]
lemma link_symm (K : Op A R) (h : ∀ F, Symm p F→ Symm p (K F)) (hu : Symm p u) (hv : Symm p v) :
    Symm p (link K b p u v) := ((h _ (hu.times hv)).sub ((h _ hu).times hv)).sub ((hu.signs _).times (h _ hv))
lemma sign_prod (q:Bool) (u v:Raw A R) : sign p q (u ⋄ v)= (sign p q u) ⋄ sign p q v := twisted_product ..
lemma link_commute (K : Op A R) (hu : Pure p false u) (hv : Pure p false v) : link K b p u v=link K b p v u:=by
    unfold link; rw [hu.central,hv.signs,hu.signs,cross_false',one_smul,one_smul,hu.central,hv.central (K u)]; abel
lemma link_commute_even (K : Op A R) (u : Raw A R) (h : Pure p false v) (hv : Pure p false (K v)) : link K false p u v=link K false p v u:=by
    unfold link; rw [h.central,sign_id,sign_id,h.central (K u),hv.central]; abel
lemma link_plus (K L : Op A R) : link (K+L) b p f g=link K b p f g+link L b p f g:=by unfold link; simp only [map_add,LinearMap.add_apply]; abel
lemma link_sum {K:I→Op A R} (s:Finset I) : link (∑ i∈s, K i) b p f g= ∑ i∈s, link (K i) b p f g:=by simp only [link,map_sum,LinearMap.sum_apply,sum_sub_distrib]
lemma link_scale (T: Op A R) (c:R) : link (c • T) b p f g=c • link T b p f g := by simp only [link,map_smul,LinearMap.smul_apply,smul_sub]
lemma link_neg (T: Op A R) : link (-T) b p f g=-(link T b p f g) := by unfold link; simp [sub_eq_add_neg, add_comm]
lemma link_add (T: Op A R) : link T b p f (u+v)= link T b p f u+ link T b p f v:=by simp only [link,map_add]; abel
lemma link_add_left (T: Op A R) : link T b p (u+v) f= link T b p u f+ link T b p v f:=by simp only [link,map_add,LinearMap.add_apply]; abel
lemma link_smul (T: Op A R) (c:R) : link T b p f (c • g)= c • link T b p f g:=by simp only [link,map_smul, smul_sub]
lemma link_smul_left (T: Op A R) (c:R) : link T b p (c • f) g= c • link T b p f g:=by simp only [link,map_smul, LinearMap.smul_apply, smul_sub]
@[simp] lemma diffPair_apply (i j : A) : diffPair i j f=D j (D i f):=rfl
lemma link_pair (i j : A) (h: (p j ^^ p i)=b) (F H : Raw A R) : link (diffPair i j) b p F H = (sign p (p j) (D i F)) ⋄ D j H + (D j (sign p (p i) F)) ⋄ D i H := by
    simp only [link,diffPair_apply,D_product,map_add,sign_twice,h]; abel
lemma link_pair_left (i j : A) (h: (p j ^^ p i)=b) (H : Raw A R) (ha:Pure p false f) :
    link (diffPair i j) b p f H = (cross (p j) (p i):R) • ((D i f) ⋄ D j H) + (D j f) ⋄ D i H := by
    rw [link_pair _ _ h, ha.signs, (ha.drop i).signs, cross_false']; simp only [one_smul,Bool.false_xor,map_smul, LinearMap.smul_apply]

/-- Pair operators also obey simple Leibniz extension inside a link on three even
vertices. Variation can also be odd if in slot `v`. -/
lemma pair_products (i j : A) (h: (p j ^^ p i)=b) (ha:Pure p false f) (hu:Pure p false u) :
   link (diffPair i j) b p f (u ⋄ v) = link (diffPair i j) b p f u ⋄ v+ u ⋄ (link (diffPair i j) b p f v) := by
   rw [link_pair_left i j h _ ha,link_pair_left i j h _ ha,link_pair_left i j h _ ha]
   have he U (W : Raw A R) : U ⋄ (u ⋄ W) = u ⋄ (U ⋄ W) := by rw [← times_assoc,← hu.central, times_assoc]
   simp only [D_product,map_add,hu.signs,cross_false',one_smul, LinearMap.add_apply, he (D i f),he (D j f), map_smul, LinearMap.smul_apply, times_assoc, smul_add]; abel

/-- Commuting loop contractions on symmetric symbols. -/
lemma exchange2 (i j a x : A) (hf : Symm p f):
    diffPair i j (diffPair a x f)=(cross (p i ^^ p j) (p a ^^ p x) : R) • diffPair a x (diffPair i j f) := by
    simp only [diffPair_apply]
    rw [(hf.drop a).commute i x,hf.commute i a,map_smul,map_smul,map_smul, ((hf.drop i).drop a).commute j x]
    -- simplification order
    rw [(hf.drop i).commute j a]; simp only [map_smul,cross_right,cross_left, smul_smul]
    simp only [cross_comm (p x) (p j),cross_comm (p a) (p j),cross_comm (p x) (p i),cross_comm (p a) (p i)]
    ring_nf
end YM.MS.Koszul
