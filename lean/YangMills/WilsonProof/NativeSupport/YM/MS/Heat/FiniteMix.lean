import YM.MS.MomentumCharge
import YangMills.WilsonProof.NativeSupport.YM.MS.WardSquares
/-!
# Polarized identities on a finite slab

Pass momentum-local (one-loop elsewhere). Left f even. No condition on ambient
 second g beyond commuting derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Set Finset Plane Koszul Flux
variable {R A P J I : Type} [CommRing R]
variable {p:Sector A}{f g h : Raw A R}
variable {Z L: Op A R} {T:Shift R p true}
local notation "Pp" =>link Z false p
local notation "Tt" =>link L true p
local notation "Q" =>T.Q
local infixl:70 " ⋄ " => product p

lemma clip_mix (hx:∀ H,Symm p H→ L (Z H)=Z (L H)) (hf:Symm p f)(hg:Symm p g)(he:Pure p false f) (hZ:Pure p false (Z f)):
    L (Pp f g)+ Tt (Z f) g + Tt f (Z g)= Z (Tt f g)+Pp (L f) g+Pp f (L g) := by
    have h := hx (f ⋄ g) (hf.times hg); rw [link_even L he (b:=true),link_even Z he (b:=false)] at h
    simp only [map_add] at h; rw [link_even L hZ (b:=true),link_even L he (b:=true),link_apply Z (L f) g (b:=false),sign_id, link_even Z he (b:=false),hx _ hf,hx _ hg] at h; linear_combination (norm:=abel) h
lemma charge_arc (hx:∀ H, Symm p H → Q (Z H)+L H= Z (Q H)) (hf:Symm p f)(hg:Symm p g)(he:Pure p false f)(hZ:Pure p false (Z f)): Q (Pp f g)+ Tt f g=Pp (Q f) g+Pp f (Q g):= by
    have h:= hx (f ⋄ g) (hf.times hg); rw [link_even Z he (b:=false), link_even L he (b:=true), T.product_rule] at h;
    simp only [T.product_rule,hZ.signs,he.signs,cross_false',one_smul,map_add] at h -- after map needed rewrite
    rw [link_apply Z (Q f) g (b:=false),sign_id,link_even Z he (b:=false),← hx _ hf,← hx _ hg] at h; simp only [map_add,LinearMap.add_apply] at h; linear_combination (norm:=abel) h

lemma pairC (i j:A)(H: Pure p false f) (ha:p i=p j) (hg:Pure p true g) : link (diffPair i j) false p (f ⋄ g) h= f ⋄ link (diffPair i j) false p g h + g ⋄ link (diffPair i j) false p f h:= by
   have ht (a b:Bool): (cross a (a ^^ b):R) *cross b a=cross a a:= by cases a <;> cases b <;> simp
   rw [link_pair i j (by simp [ha]) (f ⋄ g),link_pair i j (by simp [ha]) g,link_pair_left i j (by simp [ha]) h H]; -- inspect D second term
   rw [Pure.signs ((H.prod hg).drop i)]; simp only [Pure.signs (H.prod hg), Pure.signs hg,Pure.signs H,Pure.signs (hg.drop i), map_smul, map_add,LinearMap.add_apply,LinearMap.smul_apply, D_product, Bool.false_xor, cross_false',one_smul]; -- simp recurrence
   rw [(H.drop i).times_comm hg,(H.drop j).times_comm hg]; cases h':p j <;> simp [ha,h', times_assoc] <;> abel -- extra

section finite
variable {r:I→R}{a e:I→A}{s:Finset I}{u w:J→ A}{v:J→ R}{k:Finset J}
    (hx:Balanced p false r a e s)(hy:Balanced p true v u w k)
local notation "B" => loop r a e s
local notation "C" => loop v u w k
local notation "P0"=>link (loop r a e s) false p
local notation "C0"=>link (loop v u w k) true p
include hx
lemma LEFT (H:Pure p false f)(hu:Pure p true g) : P0 (f ⋄ g) h= f ⋄ P0 g h+g ⋄ P0 f h:= by
   simp only [loop,link_sum,map_sum,link_scale,← sum_add_distrib]; apply Finset.sum_congr rfl; intro i hi; by_cases he:r i=0; simp [he]; rw [pairC _ _ H _ hu]; simp only [map_smul, smul_add]; exact Eq.symm (by simpa using hx i hi he)
include hy
lemma press (hf:Pure p false f)(H:Symm p f)(hv:Symm p g) : C0 (P0 f f) g+(2:ℕ) • C0 f (P0 f g)=P0 (C0 f f) g+(2:ℕ) • P0 f (C0 f g):= by
    -- from clip_mix f^2.
    have he:∀ H,Symm p H→ C (B H)=B (C H):= fun _ h=>by simpa using loop_loop hy hx h
    have hm := clip_mix (Z:=B) (L:=C) (f:=f ⋄ f) he (H.times H) hv (hf.prod hf) (hx.pure (hf.prod hf)); have hxF:=hx.pure hf; have hyF:=hy.pure hf;
    rw [hx.paired_left (v:=g) hf hf, hy.paired_left (v:=g) hf hf, hy.paired_left (v:=B g) hf hf,hx.paired_left (v:=C g) hf hf,link_even B hf (b:=false),link_even C hf (b:=true)] at hm
    simp only [link_add_left,map_add] at hm; rw [show B (f ⋄ C0 f g)= _ from link_even B hf (b:=false), show C (f ⋄ P0 f g)= _ from link_even C hf (b:=true)] at hm; -- duplicates? rw all?
    rw [← hf.central (B f),← hf.central (C f)] at hm; simp_rw [hy.paired_left hxF hf, LEFT (h:=g) hx hf (show Pure p true (C f) from hyF)] at hm; -- order of paired_left
    have hy := congr_arg (fun x : Raw A R=> f ⋄ x) (clip_mix (f:=f) (g:=g) he H hv hf hxF); simp only [map_add] at hy;
    linear_combination (norm:=abel) hm - hy - hy
lemma Ppress [IsAddTorsionFree R] (hf:Pure p false f)(hh:Pure p false h)(H:Symm p f)(HH:Symm p h)(hv:Symm p g) : C0 (P0 f h) g+C0 f (P0 h g)+C0 h (P0 f g)=P0 (C0 f h) g+P0 f (C0 h g)+P0 h (C0 f g):= by
   have hu := press hx hy (hf.add hh) (H.add HH) hv; simp only [link_add,link_add_left,nsmul_add] at hu; rw [link_commute (b:=false) _ hh hf,link_commute (b:=true) _ hh hf] at hu; apply nsmul_right_injective (M:=Raw A R) (show (2:ℕ) ≠ 0 from by omega); linear_combination (norm:= (simp only [nsmul_add,two_nsmul] ; abel)) hu - press hx hy hf H hv - press hx hy hh HH hv
end finite
end YM.MS.Heat
