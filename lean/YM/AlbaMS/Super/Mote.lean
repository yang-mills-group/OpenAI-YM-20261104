import YM.AlbaMS.Super.Nerve
import Mathlib.Algebra.BigOperators.Module

/-! Left derivatives & implements graded swaps. Pure Coils. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι R E : Type*} [CommRing R] {ρ : ι→Bool} (p q : Bool)
variable (F G H : Coil ρ R) (l : List ι) (x y : ι)
namespace Coil

@[simp] lemma put_nil (c:R) : put ρ c []= c:=rfl
@[simp] lemma put_cons (c:R) : put ρ c (x::l)=0:=rfl
@[simp] lemma one_nil : (1:Coil ρ R) []=1:=rfl
@[simp] lemma one_cons : (1:Coil ρ R) (x::l)=0:=rfl
@[simp] lemma tap_mul : (F*G) []= F []* G []:=rfl
@[simp] lemma sting_read : sting p F l=sting p (F l):=by cases p <;> rfl
lemma sum_read (f : E→ Coil ρ R) (v : Finset E) : (∑ i∈v,f i) l=∑ i∈v,f i l:=
  map_sum ({toFun:= fun F : Coil ρ R=> F l,map_add':=fun _ _ =>rfl,map_zero':=rfl}:Coil ρ R→+R) f v

/-- evaluate as signed by parity or not. -/
def plane (p : Bool) : Coil ρ R →ₗ[R] Coil ρ R where
  toFun F:= ⟨tilt ρ p F,F.trusted.tilted p⟩
  map_add' _ _:= Subtype.ext (tilt_add ..)
  map_smul' _ _:= Subtype.ext (tilt_smul ..)
lemma polar : plane p F l=sting (p && band ρ l) (F l):=rfl
@[simp] lemma polar_false : plane false F=F:=rfl
lemma plane_comm : plane p (plane q F)= plane q (plane p F):=Subtype.ext (tilt_comm ..)
@[simp] lemma plane_mul : plane p (F*G)=plane p F * plane p G:=Subtype.ext (tilt_deal ..)
@[simp] lemma plane_put (c:R): plane p (put ρ c)= put ρ c:=Subtype.ext (peace_equal ..)
@[simp] lemma plane_one : plane p (1:Coil ρ R)=1:=plane_put ..

def D (x : ι) : Coil ρ R→ₗ[R] Coil ρ R where
  toFun F:= ⟨detach x F,F.trusted.det x⟩
  map_add' _ _:= rfl
  map_smul' _ _:=rfl
lemma D_read : D x F l= F (x::l):=rfl
lemma mul_cons : (F*G) (x::l) = (D x F*G) l + (plane (ρ x) F * D x G) l:=rfl
lemma mulD : D x (F*G)=D x F*G+plane (ρ x) F*D x G:=rfl
lemma planeD : D x (plane p F) = sting (p && ρ x) (plane p (D x F)):= by ext l; exact (congr_fun (detach_tilt ρ p x _) l).trans ((sting_apply _ _ _).trans (sting_read _ (plane p (D x F)) l).symm)
lemma DD : D x (D y F)=sting (ρ y && ρ x) (D y (D x F)):=by ext l; exact (congr_fun (F.trusted.top x y) l).trans ((sting_apply _ _ _).trans (sting_read _ (D y (D x F)) l).symm)
lemma D_sting : D x (sting p F)= sting p (D x F):=by cases p <;> simp
@[simp] lemma D_put (c:R): D x (put ρ c)=0:=rfl
@[simp] lemma D_one : D x (1:Coil ρ R)=0:=rfl
lemma deep (h : F []=G [])(he : ∀ x,D x F=D x G) : F=G:= ext F G (fun i=> by cases i;exact h;next x s=>exact DFunLike.congr_fun (he x) s)
/-- Pure parity, not an assertion of total weight. -/
def Tone : Prop := ∀ l, F l ≠0 → band ρ l=p
namespace Tone
variable {F G p q}
lemma none (p) : Tone p (0: Coil ρ R):=fun _ h=> False.elim (h rfl)
lemma add (h:Tone p F)(H:Tone p G): Tone p (F+G):=by
  intro l he; by_contra hu; exact he (by simp [not_not.1 (mt (h l) hu),not_not.1 (mt (H l) hu)])
lemma smul (h:Tone p F)(c:R): Tone p (c • F):=by
  intro l hh; by_contra he; exact hh (by simp [not_not.1 (mt (h l) he)])
lemma neg (h:Tone p F): Tone p (-F):=fun l ht=> h _ (fun he=>ht (by rw [neg_read,he,neg_zero]))
lemma sub (h:Tone p F)(H:Tone p G): Tone p (F-G):=sub_eq_add_neg F G ▸ h.add H.neg
lemma sum (v : Finset E)(f : E→ Coil ρ R)(h : ∀ i∈v,Tone p (f i)): Tone p (∑ i∈v,f i):=by
  induction v using Finset.induction_on with|empty=> simp [none]|@insert i t ht IH=> rw [Finset.sum_insert ht]; apply add (h i (by simp)) (IH (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
lemma dz (h:Tone p F) : Tone (xor p (ρ x)) (D x F):=by
  intro l hv; have h:= h (x::l) hv; rw [band_cons] at h; rw [←h]; cases ρ x <;> cases band ρ l <;> rfl
lemma const (c:R) : Tone false (put ρ c):=fun l h=> by cases l; rfl; exact False.elim (h rfl)
lemma one : Tone false (1:Coil ρ R):=const 1
lemma stingIt (h:Tone p F)(q) : Tone p (sting q F):=by cases q; exact h;exact h.neg
lemma pl (h:Tone p F)(q) : plane q F= sting (q && p) F := by
  ext l; rw [polar,sting_read]; by_cases t:F l=0
  · rw [t,sting_zero,sting_zero]
  rw [h l t]
lemma mul (h:Tone p F)(H:Tone q G): Tone (xor p q) (F*G):=by
  intro l; induction l generalizing F G p q with
  | nil=>
    intro hx; have he : p=false:= (h [] (left_ne_zero_of_mul (b:=G []) hx)).symm
    have hv : q=false:= (H [] (right_ne_zero_of_mul (a:= F []) hx)).symm; simp [he,hv]
  | cons x l ih=>
    intro hx; rw [mul_cons, h.pl] at hx
    by_cases ht : (D x F*G) l=0
    · rw [ht,zero_add] at hx
      rw [band_cons,ih (h.stingIt _) (H.dz x) hx]; cases p <;> cases q <;> cases ρ x <;> rfl
    rw [band_cons,ih (h.dz x) H ht]; cases p <;> cases q <;> cases ρ x <;> rfl
lemma commute (h:Tone p F)(H:Tone q G) : F*G=sting (p && q) (G*F):= by
  ext l; induction l generalizing F G p q with
  | nil=>
    rw [sting_read,tap_mul,tap_mul]; by_cases hp:F []=0
    · simp [hp]
    rw [← h [] hp]; simp [mul_comm]
  | cons x l ih=>
    -- IH on each differentiated factor
    rw [sting_read,mul_cons, mul_cons,h.pl,H.pl];
    have V := ih (h.dz x) H; have W:= ih h (H.dz x)
    rw [sting_read] at V W
    cases p <;> cases q <;> cases h:ρ x <;> simp [h,V,W,add_comm] at V W ⊢ -- improve
end Tone
end Coil
end YM.MSBar.Bric
