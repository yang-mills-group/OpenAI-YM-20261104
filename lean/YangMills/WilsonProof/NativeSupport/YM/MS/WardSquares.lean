import YM.MS.LoopIdentity
import Mathlib.Algebra.Group.Torsion

/-!
# Quantum square identities before sending stencil relations to kernels

These don't use S₂ specially. Keep both slots polarizable. `IsAddTorsionFree`
 permits formal series too. Exterior algebra signs remain in operations, no unit assumptions on coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Set Finset
variable {R A I J : Type*} [CommRing R] {p : Sector A} {u v f g : Raw A R}
local infixl:70 " ⋄ "=>product p
variable {r:I→R}{a e s}
local notation "λL" => loop r a e s
local notation "[" f ";" g "]L" => link λL true p f g

lemma minus_pass (hu:Pure p false f)(hg:Pure p true u)(i j:A)(he:(p j ^^ p i)=true) : link (diffPair i j) true p (f ⋄ u) v= f ⋄ link (diffPair i j) true p u v-u ⋄ link (diffPair i j) true p f v:= by
    have ha a : Pure p (p a) (D a f):= by simpa using hu.drop a
    have hU : Pure p true (f ⋄ u):= hu.prod hg
    rw [link_pair i j he,link_pair i j he,link_pair_left i j he v hu, sign_D p (p i) j, (hU.drop i).signs, (hU.drop j).signs, sign_D p (p i) j u, (hg.drop j).signs,(hg.drop i).signs]
    rcases pJ : p j with _|_<;> rcases pI:p i with _|_<;> simp_all (config:={failIfUnchanged:= false}) [Bool.xor,neg_smul] -- opp
    all_goals
       simp only [cross_false',one_smul,D_product, map_add, LinearMap.add_apply, neg_add_rev,hu.signs,pI,pJ,← times_assoc] -- expand cancel commute Df with u where possible
       try rw [(ha j).times_comm hg]
       try rw [(ha i).times_comm hg]
       simp [pJ,pI]
       abel

namespace Balanced
variable (h:Balanced p true r a e s)
include h
lemma quits [IsAddTorsionFree R] (hs:Symm p f) : λL (λL f)=0:= by
    have he:=loop_loop h h hs; simp only [cross_true,neg_smul,one_smul] at he
    -- term torsion point
    funext x; apply two_nsmul_eq_zero.mp; rw [two_nsmul]; exact eq_neg_iff_add_eq_zero.mp (congr_fun he x) -- lemma test
lemma antic_products (hu:Pure p false f)(hg: Pure p true u): [f ⋄ u;v]L = f ⋄ [u;v]L-u ⋄ [f;v]L:= by
    simp only [loop,link_sum,link_scale,map_sum,map_smul,← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun i hi=>?_); by_cases he:r i=0; simp [he]; rw [minus_pass hu hg _ _ (h i hi he),smul_sub]

lemma anti_j [IsAddTorsionFree R] (hu:Pure p false f)(hs:Symm p f)(hv:Symm p v): λL ([f;v]L)+ [f;λL v]L + [λL f;v]L=0:= by
    have hx := h.quits (hs.times hv); have hp : sign p true (λL f)=-λL f:= by simpa using (h.pure hu).signs true
    -- telescope
    change λL (λL (f ⋄ v))=0 at hx
    rw [link_even (b:=true) _ hu] at hx
    simp only [map_add] at hx; rw [link_apply λL (b:=true) (λL f) v,hp,link_even λL (b:=true) hu, h.quits hs,h.quits hv] at hx
    simp only [map_zero,map_neg,LinearMap.zero_apply, LinearMap.neg_apply] at hx; linear_combination (norm:=abel) hx
lemma double_j [IsAddTorsionFree R] (hu:Pure p false f)(hs:Symm p f)(hv:Symm p v): (2:ℕ) • [f;[f;v]L]L + [[f;f]L;v]L=0 := by
    have hx := h.anti_j (hu.prod hu) (hs.times hs) hv
    have hh := h.anti_j hu hs hv; have hm := congr_arg (fun x=> f ⋄ x) hh; have hu' : Pure p true (λL f):=h.pure hu
    rw [h.paired_left hu hu,h.paired_left hu hu,link_even _ hu (b:=true), ← hu.central (λL f)] at hx
    simp only [map_add,map_zero] at hm hx; rw [link_add_left,link_add_left,h.antic_products hu hu',link_even λL hu (b:=true)] at hx; linear_combination (norm:=abel) hx - hm - hm
lemma mix_j [IsAddTorsionFree R] (hu:Pure p false f)(hg:Pure p false u)(hs:Symm p f)(hr:Symm p u)(hv:Symm p v): [f;[u;v]L]L+[u;[f;v]L]L+[[f;u]L;v]L=0:= by
    have he:=h.double_j (hu.add hg) (hs.add hr) hv; have hx:=h.double_j hu hs hv; have h':=h.double_j hg hr hv
    simp_rw [link_add_left,link_add,link_commute λL hg hu,link_add_left] at he
    have hh:(2:ℕ) • ([f;[u;v]L]L+[u;[f;v]L]L+[[f;u]L;v]L)=0:= by linear_combination (norm:=abel) he - hx - h'
    funext x; exact two_nsmul_eq_zero.mp (congr_fun hh x)
end Balanced
end YM.MS.Koszul
