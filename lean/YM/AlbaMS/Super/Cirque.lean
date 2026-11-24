import YM.AlbaMS.Super.Grade
import Mathlib.LinearAlgebra.BilinearMap

/-!
Right Leibniz for cross, support & commutations. Note cross doesn't yet
carry the sign sometimes attached on the left for a BV bracket. Keeps
conventions easier with `plane p`, the parity twist of an arbitrary input.
Use formula modulo assigning correct pure Tone of *bundles* if mixing tags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι R W : Type*} [CommRing R] {ρ : ι→Bool} (p : Bool) {q e : Bool} {x y : ι}
variable {F G H : Coil ρ R} {l : List ι} {n m : ℕ} (k : ι→ι→R) (s t : Finset ι)

namespace Coil
variable {p k s}
lemma pane_tone (ht:Tone e F) (p) : Tone e (plane p F):=ht.pl p ▸ ht.stingIt _
lemma Cap.pane (h:Cap F n): Cap (plane p F) n:= fun l hv=>h l fun he=> hv (by simp [polar,he])
lemma Heg.pane (h:Heg n F): Heg n (plane p F):= fun l hv=>h l fun he=> hv (by simp [polar,he])
lemma link_rank (h:Heg (n+1) F)(ht:Heg (m+1) G): Heg (n+m) (link ρ x y F G):= ((h.D_zone x).pane.mul (ht.D_zone y)).add ((h.pane.D_zone y).mul (ht.D_zone x))
lemma link_cap (h:Cap F (n+1))(ht: Cap G (m+1)): Cap (link ρ x y F G) (n+m):=((h.dz x).pane.mul (ht.dz y)).add ((h.pane.dz y).mul (ht.dz x))
lemma cross_rank (g:Graded ρ p k)(h:Heg (n+1) F)(ht:Heg (m+1) G): Heg (n+m) (cross p k s F G):=from_cross _ _ _ _ _ g ▸ Heg.sum _ _ (fun _ _=> Heg.sum _ _ fun _ _=> (link_rank h ht).smul _)
lemma cross_cap (g:Graded ρ p k)(h:Cap F (n+1))(ht: Cap G (m+1)): Cap (cross p k s F G) (n+m):=from_cross _ _ _ _ _ g ▸ Cap.sum _ _ (fun _ _=> Cap.sum _ _ fun _ _=> (link_cap h ht).smul _)
lemma add_cross : cross p k s (F+G) H = cross p k s F H+cross p k s G H:=by simp only [cross,add_mul,map_add]; abel
lemma cross_add : cross p k s F (G+H)=cross p k s F G+cross p k s F H:=by simp only [cross,mul_add,map_add]; abel
lemma smul_cross (c:R) : cross p k s (c • F) G = c • cross p k s F G:=by simp only [cross, smul_mul_assoc,map_smul,smul_sub]
lemma cross_smul (c:R): cross p k s F (c • G)= c • cross p k s F G:=by simp only [cross, mul_smul_comm,map_smul,smul_sub]
lemma crosses (H:s⊆t)(hf:Inside (s:Set ι) F)(hg:Inside (s:Set ι) G): cross p k s F G=cross p k t F G:= by
  rw [cross,cross,touches (F*G) _ s t (hf.mul hg) H,touches F _ _ _ hf H,touches G _ _ _ hg H]
lemma cross_put_left (c:R) (g:Graded ρ p k): cross p k s (put ρ c) G=0:=by simp [from_cross p _ _ _ _ g,link]
lemma cross_put_right (c:R)(g:Graded ρ p k): cross p k s F (put ρ c)=0:=by simp [from_cross p _ _ _ _ g,link]

def tether (p : Bool)(k : ι→ι→R)(s : Finset ι): Coil ρ R →ₗ[R] Coil ρ R →ₗ[R] Coil ρ R:= LinearMap.mk₂ R (cross p k s) (fun _ _ _=> add_cross) (fun _ _ _=> smul_cross _) (fun _ _ _=>cross_add) (fun _ _ _=>cross_smul _)
@[simp] lemma from_tether : tether p k s F G=cross p k s F G:= rfl
lemma pay_across (c:R): cross p (c • k) s F G= c • cross p k s F G:=by simp only [cross,pay_touch,smul_mul_assoc,mul_smul_comm,smul_sub]
lemma add_across {k'}: cross p (k+k') s F G = cross p k s F G+cross p k' s F G:=by simp only [cross,add_touch,add_mul,mul_add];abel
lemma touch_prod : touch k s (F*G)=touch k s F*G+plane p F * touch k s G+cross p k s F G:=by unfold cross; abel
-- extension of super-commutativity to any second operand

def peel (p : Bool) (F : Coil ρ R): Coil ρ R := sift (fun l=> band ρ l=p) (fun a b h=> by
  have he : band ρ a=band ρ b := by
    clear F; induction h with
    | nil=> rfl
    | cons i h ih=> simp [ih]
    | swap i j _=>simp only [band_cons,← Bool.xor_assoc,Bool.xor_comm (ρ i) (ρ j)]
    | trans ha he ih iy=> exact ih.trans iy
  rw [he];exact id) F
lemma peel_read : peel p F l=if band ρ l=p then F l else 0:= by change @ite R _ (Classical.propDecidable _) _ _ = _; congr
lemma peel_tone : Tone p (peel p F):= by intro l hv; rw [peel_read] at hv; split at hv; assumption; exact False.elim (hv rfl)
lemma peels (F : Coil ρ R): F=peel true F+peel false F:= by ext l; rw [plus_read,peel_read,peel_read]; cases band ρ l <;> simp
lemma Tone.slider (ht:Tone e F) (G : Coil ρ R) : F*G=plane e G*F:=by
  rw [peels G,mul_add,map_add,add_mul,(peel_tone (F:=G) (p:=true)).pl,(peel_tone (F:=G) (p:=false)).pl, ht.commute (peel_tone (F:=G) (p:=true)),ht.commute (peel_tone (F:=G) (p:=false))]; cases e <;> simp

lemma cross_flip (ht:Tone e F)(h:Tone q G)(g:Graded ρ p k): cross p k s F G=sting (e && q) (cross p k s G F):=by
  unfold cross; rw [ht.pl,h.pl,ht.commute h];
  have hh:=(touch_tone _ _ _ _ s ht g).commute h; have he:=ht.commute (touch_tone _ _ _ _ s h g); cases p <;> cases e <;> cases q <;> simp [hh, he] at hh he ⊢ <;> abel

lemma link_leib (ht:Tone e F) (x y : ι)(G H : Coil ρ R):
    link ρ x y F (G*H)= link ρ x y F G * H + plane (xor e (xor (ρ x) (ρ y))) G * link ρ x y F H:=by
  have hh:= (pane_tone (ht.dz x) (ρ y)).slider (plane (ρ y) G)
  have he := ((pane_tone ht (ρ x)).dz y).slider (plane (ρ x) G)
  unfold link; rw [mulD,mulD,mul_add,mul_add,← mul_assoc (plane _ _) (D y G),← mul_assoc (D y (plane _ _)) (D x G)]
  rw [← mul_assoc (plane _ _) (plane _ _),← mul_assoc (D y (plane _ _)) (plane _ _),hh,he,plane_twice,plane_twice]
  rw [show xor (xor e (ρ x)) (ρ y)=xor e (xor (ρ x) (ρ y)) by simp,
      show xor (xor e (ρ y)) (ρ x)=xor e (xor (ρ x) (ρ y)) by simp [Bool.xor_comm (ρ y) (ρ x)]]
  simp only [mul_add,add_mul,mul_assoc]; abel
lemma cross_leib (ht:Tone e F)(g:Graded ρ p k): cross p k s F (G*H)= cross p k s F G*H + plane (xor e p) G * cross p k s F H:=by
  rw [from_cross _ _ _ _ _ g,from_cross _ _ _ _ _ g, from_cross _ _ _ _ _ g]; simp_rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; by_cases he:k i j=0
  · simp [he]
  rw [link_leib ht,g i j he,smul_add,smul_mul_assoc,mul_smul_comm];
end Coil
end YM.MSBar.Bric
