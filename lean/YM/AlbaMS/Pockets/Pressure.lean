import YM.AlbaMS.Pockets.Vessel
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# generating the coefficient path. Use double debt for each extra power

pack leaves rank at engineering cap (not observable-normalized). Pressure on
vertical tag now finite, can use same supports checking linear gauge identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function IsNilpotent
open scoped BigOperators Classical
variable {ι K W R : Type*} [Fintype K] [AddCommMonoid W] [CommRing R] {ρ : ι→Bool}
open Coil
namespace Coil
variable {F G : Coil ρ R} {a b h q i j : ℕ} {k : ι→ι→R} {p : Bool} {s : Finset ι} {x : ι} {D : Ladder K W}

def Thin (m n : ℕ)(F : Coil ρ R):Prop:=∀ l,F l≠0→ m+l.length ≤ n
namespace Thin
lemma none : Thin a b (0:Coil ρ R):= fun _ hh=> False.elim (hh rfl)
lemma cheap (h:Cap F b): Thin 0 b F:= fun _ t=> Nat.zero_add _ ▸ h _ t
lemma cap (h:Thin a b F): Cap F b :=fun _ t=> le_trans (Nat.le_add_left ..) (h _ t)
lemma impossible (h:Thin a b F)(H:b<a): F=0:=Coil.ext _ _ (fun l=>not_not.1 fun (he : F l≠0)=> by have hv:=h l he;omega)
lemma add (h:Thin a b F)(H:Thin a b G):Thin a b (F+G):=by intro l hv; by_cases ht:F l=0;exact H l (fun hu=> hv (by simp [ht,hu])); exact h l ht
lemma smul (h:Thin a b F)(c:R): Thin a b (c • F):=fun l hv=> h l (fun hu=> hv (by simp [hu]))
lemma neg (h:Thin a b F): Thin a b (-F):= fun l hv=> h l (fun hu=> hv (by simp [hu]))
lemma sub (h:Thin a b F)(H:Thin a b G):Thin a b (F-G):= sub_eq_add_neg F G ▸ h.add H.neg
lemma sum {E : Type*}(v:Finset E)(f:E→ Coil ρ R)(h:∀ i∈v,Thin a b (f i)):Thin a b (∑ i∈v,f i):=by induction v using Finset.induction_on with|empty=>simp [none]|@insert i t ht IH=>rw [Finset.sum_insert ht]; apply add (h i (by simp)) (IH (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
lemma plane (h:Thin a b F): Thin a b (plane p F):= fun l hv=>h l (fun hu=>hv (by simp [polar,hu]))
lemma d (h:Thin a b F): Thin (a+1) b (Coil.D x F) := by intro l he; have ht:=h (x::l) he; rw [List.length_cons] at ht; omega
lemma mul (hm:Thin a b F)(H:Thin h q G): Thin (a+h) (b+q) (F*G):=by intro l hv; obtain ⟨i,j,hi,hj,he⟩:=occurred F G hv; rw [he.length_eq,List.length_append]; have hu:=hm i hi; have ht:=H j hj; omega
lemma touch (h:Thin a b F): Thin (a+2) b (touch k s F):= by rw [touch_apply]; exact Thin.sum _ _ (fun i _=> Thin.sum _ _ fun j _=>(h.d.d.smul (k i j)))
lemma cross (hv:Graded ρ p k)(hm:Thin a b F)(H:Thin h q G): Thin (a+h+2) (b+q) (cross p k s F G):=by
  rw [from_cross _ _ _ _ _ hv]; refine Thin.sum _ _ (fun i _=>Thin.sum _ _ fun j _=>?_); rw [show a+h+2=a+1+(h+1) by omega]; exact ((hm.d.plane.mul H.d).add (hm.plane.d.mul H.d)).smul _
end Thin
end Coil
variable [Algebra ℚ R]
namespace Ladder
variable {F G H : Coil ρ R} {a b c h i j N n : ℕ} {s : Finset ι} {ρ : ι→Bool}
variable {D : Ladder K W} {p : Bool} {x : K}

-- since applications need summable bands polynomial degree, use general commute engine

def patch (R : Type*) [CommRing R] [Algebra ℚ R](i:ℕ):= algebraMap ℚ R (↑(i+1):ℚ)⁻¹
lemma patch_succ (i:ℕ): ((i+1:ℕ):R)*patch R i=1:=by unfold patch;rw [← map_natCast (algebraMap ℚ R),← map_mul]; field_simp; simp

def brink (g : ι→ι→R)(s : Finset ι) (F : ℕ→ Coil ρ R)(i:ℕ): Coil ρ R:= patch R i • (touch g s (F i)-halve R • ∑ j∈ Finset.antidiagonal i,cross false g s (F j.1) (F j.2))
def ev (g : ι→ι→R)(s : Finset ι)(F : Coil ρ R): ℕ → Coil ρ R
 | 0=>F
 | i+1=> brink g s (fun j=> if j<i+1 then ev g s F j else 0) i
-- need dependent if to prove termination
 termination_by n=>n
lemma ev_succ {g : ι→ι→R}: ev g s F (i+1)=brink g s (ev g s F) i:=by
  rw [ev]; unfold brink; simp only [Nat.lt_add_one,if_true];
  congr 3; refine Finset.sum_congr rfl fun x hx=>?_ ; rw [Finset.mem_antidiagonal] at hx; rw [if_pos (by omega),if_pos (by omega)]
-- when interpreting equations coefficient of every tag
variable {U V: Coil ρ (Tags D R)} {g : ι→ι→R}
def Track0 (D : Ladder K W)(g : ι→ι→R)(s : Finset ι)(U : ℕ→ K→ Coil ρ R)(i:ℕ)(x:K):= patch R i • (touch g s (U i x)-halve R • ∑ j∈ Finset.antidiagonal i, ∑ y∈ D.sums x, cross false g s (U j.1 y.1) (U j.2 y.2))
lemma brinks {U : ℕ→ Coil ρ (Tags D R)} (hk:Graded ρ false g): clip D x (brink (D.rail g) s U i)=Track0 D g s (fun j x=>clip D x (U j)) i x:=by unfold brink Track0; have he : ∀ q : ℚ, algebraMap ℚ (Tags D R) q= Tags.inject D (algebraMap ℚ R q):=fun _=>rfl; simp only [patch,halve,he,clip_scale,map_sum,map_sub,clip_touch,clip_cross hk]
lemma electric (h:∀ x,Thin 0 (b*D.d x) (clip D x U))(hv:Graded ρ false g) : Thin (2*i) (b*D.d x) (clip D x (ev (D.rail g) s U i)):=by
  induction i using Nat.strong_induction_on generalizing x with | h i ih=>
    cases i; rw [ev,Nat.mul_zero]; apply h
    next j=>
      rw [ev_succ,brinks hv]; simp only [Track0]; refine (Thin.sub ?_ (Thin.smul ?_ _)).smul _
      · rw [Nat.mul_add,mul_one];exact (ih j (Nat.lt_succ_self _)).touch
      refine Thin.sum _ _ (fun i hi => Thin.sum _ _ fun l hl=>?_); rw [Finset.mem_antidiagonal] at hi; have he:= D.raises' ((D.member ..).1 hl); rw [he,mul_add b, show (2*(j+1):ℕ)=2*i.1+2*i.2+2 by omega]; exact Thin.cross hv (ih i.1 (by omega)) (ih i.2 (by omega))
end Ladder
end YM.MSBar.Bric
