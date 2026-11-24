import YM.AlbaMS.Super.Cirque
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Data.Rat.Cast.CharZero
/-!
A few BV identities (odd constant-coefficient contraction).
Use rational scalars for ℚ rescue despite ring R may have zerodivisors. This
arises with external mask variables suppressed before projection, which are
commuting and may be nilpotent. Everything here valid with values continued to
complex scalars or formal variables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι R : Type*} [CommRing R] {ρ : ι→Bool} {p q e : Bool} {x y : ι}
variable {F G H S : Coil ρ R} {l : List ι} {n m : ℕ} {k : ι→ι→R} {s : Finset ι}
namespace Coil
lemma main_product_even (p) (h:Tone false F): touch k s (F*G) = touch k s F*G + F*touch k s G + cross p k s F G:=by rw [touch_prod (p:=p)];simp [h.pl]
lemma odd_product (h:Tone true F): touch k s (F*G) = touch k s F*G - F*touch k s G+cross true k s F G:=by rw [touch_prod (p:=true),h.pl]; simp [sub_eq_add_neg]
lemma uses (h : Graded ρ true k)(ht:Tone false F):cross true k s F (G*H)= cross true k s F G*H + plane true G * cross true k s F H:= cross_leib ht h
variable [Algebra ℚ R]
def halve (R : Type*) [CommRing R] [Algebra ℚ R] : R:= algebraMap ℚ R (1/2)
lemma halve_twice : (halve R+halve R)=1:= by unfold halve; rw [← map_add]; norm_num
lemma twice_halve (F : Coil ρ R): halve R • (F+F)=F:=by rw [smul_add,← add_smul,halve_twice,one_smul]
lemma touch_sq (F : Coil ρ R)(h:Graded ρ true k): touch k s (touch k s F)=0:=by
  let T:= touch k s (touch k s F); change T=0
  have ha:T+T=0:= eq_neg_iff_add_eq_zero.mp (touch_touch _ _ _ _ _ _ _ h h)
  rw [← twice_halve T,ha,smul_zero]
lemma touch_odd_cross (h:Graded ρ true k)(ht:Tone false F): touch k s (cross true k s F G)+cross true k s F (touch k s G)+cross true k s (touch k s F) G=0:=by
  have hh : Tone true (touch k s F):= touch_tone _ _ _ _ _ ht h
  have he:= touch_sq (s:=s) (F*G) h
  rw [main_product_even true ht,map_add,map_add,odd_product hh, main_product_even true ht,touch_sq _ h,touch_sq _ h,zero_mul,mul_zero,zero_sub,add_zero] at he
  exact (_root_.Eq.trans (b:=_) (show _ = -(_ * _ : Coil ρ R) + cross true k s (touch k s F) G + (touch k s F*touch k s G+cross true k s F (touch k s G))+touch k s (cross true k s F G) from by abel) he) -- fix
lemma odd_square (h:Graded ρ true k)(ht:Tone false S): cross true k s S (cross true k s S G) = -(halve R) • cross true k s (cross true k s S S) G:=by
  let M (G H : Coil ρ R):= cross true k s G H
  let T:= touch (ρ:=ρ) k s; have ha : Tone true (M S S):= tone_cross _ _ _ _ _ ht ht h
  have hu:Tone true (T S):= touch_tone _ _ _ _ _ ht h
  have a:= touch_odd_cross (s:=s) (G:=S*G) h ht
  -- expand and cancel
  rw [uses h ht,ht.pl,map_add, main_product_even true ht,cross_add,cross_add] at a -- main_product target selection
  dsimp only [T,M] at hu ha
  change M S (M S G) = _
  simp only [Bool.and_false,sting_false] at a; rw [odd_product ha,main_product_even true ht, uses h ht,uses h ht,cross_leib hu h,ht.pl true,Bool.and_false,sting_false, hu.pl true,Bool.true_and,sting_true,show xor true true=false from rfl,polar_false] at a
  have he : (T (M S S)+M S (T S)+M (T S) S)*G + S*(T (M S G)+M S (T G)+M (T S) G)+ (M (M S S) G+(M S (M S G)+M S (M S G))) =0:=by
    apply Eq.trans _ a; simp only [add_mul,mul_add,neg_mul,M,T]; abel
  rw [show T (M S S)+M S (T S)+M (T S) S=0 from touch_odd_cross h ht,show T (M S G)+M S (T G)+M (T S) G=0 from touch_odd_cross h ht, zero_mul,mul_zero,zero_add,zero_add,add_comm (M _ _)] at he
  rw [← twice_halve (M S (M S G)), eq_neg_iff_add_eq_zero.mpr he, smul_neg,neg_smul]
def master (k : ι→ι→R)(s : Finset ι)(S : Coil ρ R):=halve R • cross true k s S S-touch k s S
def quantum (k : ι→ι→R)(s : Finset ι)(S : Coil ρ R) : Coil ρ R→ₗ[R] Coil ρ R:= tether true k s S - touch k s
omit [Algebra ℚ R] in
lemma quantum_apply : quantum k s S G=cross true k s S G-touch k s G:=rfl
lemma quantum_sq (h:Graded ρ true k)(ht:Tone false S): quantum k s S (quantum k s S G)= -cross true k s (master k s S) G:=by
  simp_rw [quantum, LinearMap.sub_apply,map_sub,touch_sq _ h,from_tether,master];
  rw [odd_square h ht, ← from_tether (F:=_ - touch k s S) (G:=G), map_sub] -- fix
  simp only [sub_zero,LinearMap.sub_apply,from_tether,smul_cross,neg_smul]; rw [eq_neg_iff_add_eq_zero]; rw [show cross true k s ((touch k s) S) G= - (touch k s (cross true k s S G)+cross true k s S (touch k s G)) from eq_neg_of_add_eq_zero_right (touch_odd_cross h ht)]; abel
lemma nil_sq (h:Graded ρ true k)(ht:Tone false S)(H:master k s S=0): quantum k s S (quantum k s S G)=0:=by rw [quantum_sq h ht,H,cross];simp
end Coil
end YM.MSBar.Bric
