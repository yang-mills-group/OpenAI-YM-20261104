import YM.MS.Book.Mask
import YM.MS.Cylinder.Characters
import Mathlib.Algebra.BigOperators.NatAntidiagonal
/-!
# Rank restrictions and germ convolution

Pull out fixed length Taylor bodies inside bilinear operations. `ℤ` avoid
 conventions on negative estimates. Shift operators link test soon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book
open Function Filter Set Finset Plane Koszul Cylinder Lab
variable {A P B R: Type*} [CommRing R] {p:Sector A}
variable {F H: Raw A R} {f: Seed A P R} {h hx:ℤ}

-- restrict raw.
lemma conn (i:A): D i (mask h F)= mask (h-1) (D i F):= by ext l; by_cases he:(l.length:ℤ) = h-1; rw [at_D,enough _ (by simp; omega),enough _ he,at_D]; rw [at_D,strange _ (by simp; omega),strange _ he]
lemma sign (i:Bool): Koszul.sign p i (mask h F)= mask h (Koszul.sign p i F):= by ext l; by_cases he:(l.length:ℤ)=h; simp only [at_sign,enough _ he]; simp only [at_sign,strange _ he,mul_zero]
lemma maskUses {s:Set A}(h':Uses s F): Uses s (mask h F):= by intro l i hv he; by_cases H:(l.length:ℤ)=h; rw [enough _ H,h' l i hv he]; exact strange _ H

def model (h:ℤ) : Cyl A R→ₗ[R] Cyl A R:= ((mask h).comp (Stack _ _).subtype).codRestrict (Stack _ _) (fun v=> by obtain ⟨s,hs⟩:=fromCyl v; exact packed (maskUses hs))
lemma mask_s (F:Cyl A R): (model h F).val=mask h F.val:= rfl
lemma mod_ink (F:Cyl A R)(T:B→A→R): shade T (model h F)= mask h (shade T F):= by
    funext l; induction l generalizing h F with
    | nil=> simp [mask,mask_s];
    | cons i l ih=>
       obtain ⟨s,hs⟩:=fromCyl F; rw [D_eval i (shade T _),shade_drop _ _ (F:=model h F) (maskUses hs),D_eval i (mask h _),conn,shade_drop _ i F hs]; simp_rw [Finset.sum_apply,Pi.smul_apply,show ∀ x:A,enter x (model h F)=model (h-1) (enter x F) from fun x=>Subtype.ext (conn x), ih, map_sum,Finset.sum_apply,map_smul,Pi.smul_apply]
lemma mod_ferry (F:Cyl A R)(r:A→B): Ferry r (model h F)=model h (Ferry r F):= Subtype.ext (mod_ink F (way r))
lemma mod_tag (F:Cyl A R)(c:A→R): graffiti c (model h F)=model h (graffiti c F):= by apply Subtype.ext; funext l; by_cases he:(l.length:ℤ)=h; simp only [landc,rent,mask_s,enough _ he]; simp only [landc,rent,mask_s,strange _ he,mul_zero]

lemma rank_off (hF:rank h F) (h:h≠hx) : mask hx F=0:= by
   ext l; by_cases hz:(l.length:ℤ)=hx; rw [enough _ hz]; exact hF _ (by rw [mod_int,hz]; exact Ne.symm h); exact strange _ hz
-- minRank `from n` all components at least h.
def From (F : Raw A R)(h:ℤ):= ∀ l,(l.length:ℤ) < h → F l=0
def Limit (F:Raw A R)(h:ℤ):=∀ l,(l.length:ℤ)>h→F l=0
namespace From
lemma add (hF:From F h)(hH:From H h): From (F+H) h :=fun l hl=>by rw [Pi.add_apply,hF l hl,hH l hl,add_zero]
lemma sum (J:Finset B){f:B→Raw A R}(H:∀ i∈J,From (f i) h): From (∑ i∈J,f i) h:= by intro l he; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun i hi=> H i hi l he
lemma smul (c:R)(hF:From F h): From (c • F) h:= fun l hl=> by simp [hF l hl]
lemma signs (hF:From F h)(b:Bool): From (Koszul.sign p b F) h:=fun l hl=>by simp [hF l hl]
lemma pair (hF:From F h)(hH:From H hx): From (Koszul.product p F H) (h+hx):= by
    intro l hv; rw [scattered,scatter_congr _ l _ (fun _ _=>(0:R)) ?_]; exact map_zero (allocate ..)
    intro a b hL; have he:= split_length hL; by_cases ht:(a.length:ℤ)≥h -- name conflict
    · rw [hH _ (by omega),mul_zero]
    rw [hF _ (by omega),zero_mul]
lemma tag (H:From F h)(v:ℤ) : From (mask v F) h:= by intro l he; by_cases hl:(l.length:ℤ)=v; exact (enough _ hl).trans (H l he); exact strange _ hl
lemma tip (hF:From F h)(i:A): From (D i F) (h-1):= fun l he=> hF _ (by simp; omega)
end From
namespace Limit
lemma add (hF:Limit F h)(hH: Limit H h): Limit (F+H) h:= fun l hl=> by rw [Pi.add_apply,hF l hl,hH l hl,add_zero]
lemma sub (hF:Limit F h)(hH: Limit H h): Limit (F-H) h:= fun l hl=> by rw [Pi.sub_apply,hF l hl,hH l hl,sub_self]
lemma sum (J:Finset B){f:B→ Raw A R}(H:∀ i∈J, Limit (f i) h): Limit (∑ i∈J,f i) h:= by intro l he; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun i hi=> H i hi l he
lemma smul (c:R)(hF:Limit F h): Limit (c • F) h:= fun l hl=>by simp [hF l hl]
lemma up (hF:Limit F h)(he:h≤hx): Limit F hx:= fun l hl=> hF l (by omega)
lemma mod (F:Raw A R)(h:ℤ): Limit (mask h F) h:=fun l hl=> strange l (by omega)
lemma pair (hF:Limit F h)(hH:Limit H hx): Limit (product p F H) (h+hx):= by
   intro l he; rw [scattered,scatter_congr _ l _ (fun _ _=>(0:R)) ?_]; exact map_zero (allocate ..)
   intro a b hh; have hp:=split_length hh; by_cases hu:(a.length:ℤ)≤h
   · rw [hH _ (by omega),mul_zero];
   rw [hF _ (by omega),zero_mul]
lemma tip (hF:Limit F h)(i:A): Limit (D i F) (h-1):=fun l he=> hF _ (by simp; omega)
lemma signs (hF:Limit F h)(b:Bool): Limit (Koszul.sign p b F) h:= fun l hl=>by simp [hF l hl]
lemma shades (F:Cyl A R)(hF:Limit F.val h)(T:B→A→R): Limit (shade T F) h:= by
   intro l he; rw [← enough l (F:=shade T F) (show (l.length:ℤ)=l.length from rfl),← mod_ink]; have hp : model (l.length:ℤ) F=0:= by
       apply Subtype.ext; ext k; by_cases hx:(k.length:ℤ)=l.length; exact (enough k hx).trans (hF k (by omega)); exact strange _ hx
   rw [hp,map_zero]; rfl
end Limit
end YM.MS.Book
