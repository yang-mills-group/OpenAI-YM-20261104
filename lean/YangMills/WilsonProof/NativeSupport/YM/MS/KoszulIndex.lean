import YM.MS.KoszulIndex
import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Variable
import YM.MS.Local.Number
import YM.MS.Local.Finite
import YM.MS.Local.ExactSpan
import YM.MS.Local.String
import YM.MS.Local.Monomial
import YM.MS.Local.Tile
import YM.MS.Roles
import YangMills.WilsonProof.NativeSupport.YM.MS.Color.Components

/-!
# Additional integer grading on raw (rank also instance)

Keep ghost parity in rules, and odd primitive marks. No Grassmann square issues.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Filter Finset Set Cylinder
open scoped Topology
variable {A B R:Type*}[CommRing R] {F G : Raw A R} {p:Sector A}{v : A→ℤ}{h h':ℤ}

@[simp] lemma charge_empty : chargeInt v []=0:= rfl
lemma elementary (v:A→ℤ)(l:Legs A)(hp:∀ i,Local.parity (v i)=p i): degree p l=Local.parity (chargeInt v l):= by induction l with| nil=>rfl| cons i l ih=> simp only [degree_cons,charge_int,ih,Local.par_add,hp] -- universe?
namespace Rails
lemma enter (i:A)(H:Rails v h F): Rails v (h-v i) (D i F):=by intro l he; exact H (i::l) (by rw [charge_int]; omega)
lemma sign (H:Rails v h F)(b:Bool): Rails v h (sign p b F):= fun l hl=> by simp [H l hl]
lemma add (H:Rails v h F)(K:Rails v h G): Rails v h (F+G):=fun l hl=> by simp [H l hl,K l hl]
lemma zero : Rails v h (0:Raw A R):=fun _ _=> rfl
lemma product (H:Rails v h F)(K: Rails v h' G): Rails v (h+h') (product p F G):= by
    intro l hl; rw [scattered, scatter_congr _ l _ (fun _ _=> (0:R)) ?_]; swap
    · intro l r he; by_cases hh: chargeInt v l=h; swap; · rw [H l hh,zero_mul]
      rw [K r (fun hq=> hl ( (show chargeInt v l + chargeInt v r= _ from split_sum v he).symm.trans (congr_arg₂ _ hh hq))),mul_zero]
    exact map_zero (allocate ..)
lemma shades {T:B→A→R}{w:B→ℤ} (F:Cyl A R)(H:Rails v h F.val)(ht:∀ i j, T i j≠0→ w i=v j): Rails w h (shade T F):= by
   intro l hl; induction l generalizing F h with
   | nil=> rw [shade_nil]; exact H [] hl
   | cons i l ih=> obtain ⟨s,hs⟩:=fromCyl F; rw [deriv_lum T _ _ hs]; refine Finset.sum_eq_zero (fun j hj=> ?_); by_cases hx:T i j=0; simp [hx]; rw [ih (Cylinder.enter j F) (H.enter _) (fun q=> hl (by rw [charge_int, ht _ _ hx,q]; omega)),mul_zero]
lemma ferry {w:B→ℤ}(r:A→B)(h':∀ i,v i=w (r i))(F:Cyl A R)(H:Rails v h F.val): Rails w h (Ferry r F).val:= shades _ H fun i j hi=> (show i=r j from Classical.byContradiction fun he=> hi (need _ he)) ▸ (h' j).symm
lemma tags (c:A→R)(F:Cyl A R)(H:Rails v h F.val): Rails v h (graffiti c F).val:= fun l hl=> by simp [landc,rent,H l hl]
lemma coin (c:R): Rails v 0 (Koszul.coin c):= by intro l hl; cases l; contradiction; rfl
lemma letter (i:A): Rails v (v i) (atLetter i (R:=R)):= by
    intro l hl; cases l with| nil=>rfl | cons a l=> cases l with| nil=> exact notNamed _ (fun h=> hl (by simp [h]))| cons b l=> rfl
lemma parity (hp:∀ i,Local.parity (v i)=p i)(hF:Rails v h F): Pure p (Local.parity h) F:= fun l hl=> hF l (fun he=> hl ( (elementary v l hp).trans (congr_arg Local.parity he)))
end Rails
end YM.MS.Koszul
