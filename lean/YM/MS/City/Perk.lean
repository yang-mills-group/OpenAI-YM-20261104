import YM.MS.City.Fringes
/-!
# Translation almost-periodic symbol heights

Recover full cycles from weighted symmetric stencil on all real momenta. No total-momentum guard.
 Necessary for recovering all grid estimates also. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F H: Landau.Detect.Law G} {K L: Flux (Branch G Axis) QP ℂ} {b: Bool}
namespace Perk
lemma funds (h:Perk F)(p:QP)(x:Cover)(l r i): F (l++(i,p-rep x)::r)=veil x i*F (l++(i,p)::r):= by rw [sub_eq_add_neg,← map_neg,h,backv]
lemma spin (c:ℂ)(h:Perk F): Perk (c • F):= by intro i j k s t; simp only [Pi.smul_apply,h i j k s t,smul_eq_mul]; ring
lemma add (h:Perk F)(h':Perk H): Perk (F+H):=fun l r i p q=>by simp only [Pi.add_apply,h l r i p q,h' l r i p q,mul_add]
lemma coin (c:ℂ): Perk (Koszul.coin c: Landau.Detect.Law G):= by intro l r i p q; cases l <;> simp [Koszul.coin]
lemma zeros : Perk (0:Landau.Detect.Law G):= by intro l r i p q; simp
lemma sum {I:Type*}{F:I→ Landau.Detect.Law G} (s: Finset I)(h:∀ i∈s,Perk (F i)): Perk (∑ i∈s,F i):= by intro l r i p q; rw [Finset.sum_apply,Finset.sum_apply,Finset.mul_sum]; exact Finset.sum_congr rfl (fun i hi=> h i hi ..)
-- extension from head for Sym.
lemma from_head (h: Symm (field parity) F) (ht:∀ i p q r,F ((i,p+rep q)::r)=veil q i*F ((i,p)::r)): Perk F:= by
   intro l r i p q; induction l using List.reverseRecOn generalizing r with
   | nil=>simp [ht]
   | append_singleton l a ih=> rw [List.append_assoc,List.append_assoc]; change F (l++a::(i,p+rep q)::r)=_ * F (l++a::(i,p)::r); rw [h,ih,show F (l++a::(i,p)::r)=_ from h l a (i,p) r]; unfold field; ring
lemma perk_origin (F: Dot G Cover)(h:Symm Draft.DotFlip F.val): Perk (Tone.run F):= from_head (tied.sym F h) fun i p q r=> (by exact congr_fun (consensual F p i q) r)
lemma perk_t (h: Perk F)(K:Flux (Branch G Axis) QP ℂ) (q:QP): Perk (trc K q F):= by
   simp_rw [trc,LinearMap.sum_apply, LinearMap.smul_apply]; refine sum _ (fun i _=> sum _ (fun j _=> spin _ ?_)); intro l r k p u; exact h ((i,q)::(j,-q)::l) r k p u
lemma loop (μ:Measure QP)(h:Perk F): Perk (Ccy K F μ):= by
    intro l r a p u; unfold Ccy; simp_rw [(perk_t h K _ ) l r a p u,integral_const_mul] -- not trigger

variable (x:Cover)(q:QP)(a e i j:Branch G Axis)(l r:Legs (LightMode G QP))
private lemma pin (hk:Near K)(u:QP)(x:Cover)(i j): K i j (u-rep x)=veil x i*veil x j*K i j u:= by rw [sub_eq_add_neg,← map_neg,hk]; simp [backv]
lemma fee1 (h:Perk F)(ht:Perk H)(hK: Near K) : radius parity K i j F H ((a,q+rep x)::l) r= veil x a * radius parity K i j F H ((a,q)::l) r:= by
    unfold radius; simp only [net_cons,degree_cons,field]; rw [show -(q+rep x+net l) = -(q+net l)-rep x by abel, show -(-(q+net l)-rep x) = - (-(q+net l))+ rep x by abel, pin hK];
    simp_rw [show ∀ H:Legs (LightMode G QP), F ((i, -(q+net l)-rep x)::H)= _ from fun l'=> funds h (-(q+net l)) x [] l' i, show H ((j, - (-(q+net l))+rep x)::r)=_ from ht [] r j _ x]; simp only [List.nil_append]; rw [show F ((i,-(q+net l))::(a,q+rep x)::l)= _ from h [(i,_)] l a q x]; -- parse nil append
    simp only [List.nil_append,List.cons_append]; ring_nf; simp only [pow_two,testX,mul_one,one_mul] -- apply cancellations
lemma fee2 (ht:Perk H) : radius parity K i j F H l ((a,q+rep x)::r)= veil x a*radius parity K i j F H l ((a,q)::r):= by unfold radius; dsimp only; rw [show H (_::(a,q+rep x)::r)= _ from ht [(j,- - net l)] r a q x]; simp only [List.cons_append,List.nil_append]; ring

lemma keeper (h:Perk F)(ht:Perk H)(hp:Symm (field parity) F)(hh:Symm (field parity) H)(hx:Near K)(hr: Reverse K parity)(hc:closed K parity b): Perk (tree parity K F H):= by
   refine from_head (tree_sym hc hp hh) (fun i p q r=>?_); unfold tree; simp_rw [scatter_cons,convertR hr]; let T:=allocate (field parity) r (R:=ℂ); change T _= veil q i • T _; rw [← map_smul]; congr! 2; funext u; simp_rw [Pi.smul_apply, smul_eq_mul,fee1 q p i _ _ _ _ h ht hx, fee2 q p i _ _ _ _ ht, ← Finset.mul_sum]; unfold field; ring
lemma hit_steps (h: Perk F)(hh: Perk H)(hx:Near K)(hk:Near L): hits parity K L F H l r a e i j (q+rep x)= hits parity K L F H l r a e i j q:= by
   -- use fee1 fee2 directly
   unfold hits; rw [hk,fee1 x q a i j _ _ h hh hx,neg_add,← map_neg,fee2 (-x) (-q) e i j _ r hh,backv]; ring_nf; simp [pow_two,testX]
end Perk
end YM.MS.City
