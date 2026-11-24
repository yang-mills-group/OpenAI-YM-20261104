import YM.Contacts.Milling.Tower
/-! # Composite rooted lift. Repeat a given wire use (Faa), no loss here. -/
namespace YM.Contacts.Barrage
open Function Set Finset Filter RG Wilson Lattice Precision Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge
open scoped Topology BigOperators MeasureTheory Matrix Classical NNReal
noncomputable section
variable {X Y α β ι κ:Type}{b:ℝ}{f: Field ι X}{l: Pulse.Range X}
section
variable (p:κ → ι)(h:Surjective p)
private def tube (h:Surjective p)(X:Type) : (ι→X) ↪ (κ→X):= ⟨(· ∘ p), fun _ _ H=> funext (h.forall.mpr fun i=> congr_fun H i)⟩
private def tubes (h:Surjective p) (i:κ)(x:X): Locked X (p i) x ↪ Locked X i x:= ⟨fun y=> ⟨y.val∘p,y.property⟩, fun _ _ H=>Subtype.ext ((tube p h X).injective (congr_arg Subtype.val H))⟩
def fans (F : Field ι X) : Field κ X:= fun y=> if H:y∈ Set.range (fun x:ι→X=> x∘p) then F H.choose else 0
include h
lemma fans_read (f:Field ι X)(x:ι→X): fans p f (x∘p)= f x:= by
   unfold fans; split
   next hd=> congr; apply (tube p h X).injective; exact hd.choose_spec
   next hh=> exact (hh ⟨x,rfl⟩).elim
private lemma outside (f:Field ι X)(z:Locked X i x) (hu:z∉ Set.range (tubes p h i x)): fans p f z.val=0:= dif_neg (fun ⟨y,hy⟩=> hu ⟨⟨y,(show y (p i)=_ from (congr_fun hy i).trans z.property)⟩,Subtype.ext hy⟩) -- auto
lemma fans_shadow {q:X→Y}{g:Field ι Y}(H: Shadow q f g): Shadow q (fans p f) (fans p g):= by
  intro i x y; let U:=tubes p h i x; let V:=tubes p h i (q x); have hv(z): roll q _ _ (U z)= V (roll q _ x z):= rfl
  rw [MergeProof.expand_eq,←U.injective.tsum_eq]; swap; · intro z hz; by_contra hw; apply hz; dsimp only; rw [outside p h _ _ hw,ite_self]
  simp_rw [show ∀ z, roll q _ _ (U z)= _ from hv, show ∀ z,fans p f (U z).val=f z.val from fun z=> fans_read p h f z.val]; by_cases hj:y∈Set.range V
  · obtain ⟨z,rfl⟩:= hj; rw [show fans p g (V z).val=_ from fans_read p h g z.val]; simp_rw [V.injective.eq_iff]; exact (H (p i) x z).trans (expand_eq ..)
  rw [outside p h _ _ hj]; simp only [fun z=> ne_of_mem_of_not_mem (show V z∈Set.range V from Set.mem_range_self _) hj, ↓reduceIte,tsum_zero]
lemma fans_mirror {e:Equiv.Perm X}(H:Mirrored e f): Mirrored e (fans p f):= by
   intro x; by_cases hx:x∈ Set.range (tube p h X)
   · obtain ⟨i,rfl⟩:= hx; change fans p f ((e∘ i)∘p)= fans p f (i∘p); rw [fans_read p h _, fans_read p h _, H];
   rw [show fans p f x=0 from dif_neg (show ¬ x ∈Set.range (fun x:ι→X=> x ∘ p) from hx), fans, dif_neg ?_]; rintro ⟨y,hy⟩; refine hx ⟨e.symm ∘ y, funext fun i=> e.symm_apply_eq.mpr (congr_fun hy i)⟩
variable [Fintype κ][Fintype ι]
lemma fans_root (H:Rooted l f b): Rooted l (fans p f) b:= by
   refine ⟨H.cash,fun i x=>?_⟩; let F (z:Locked X i x) := ‖fans p f z.val‖ * l.bill z.val; let G (z:Locked X (p i) x) := ‖f z.val‖*l.bill z.val; let U:=tubes p h i x
   have he: G= F ∘ U:= funext fun t=> by change _= ‖fans p f (t.val ∘ p)‖*l.bill (t.val ∘ p); rw [fans_read p h _,l.retrieve _ _ h]
   have hp:= H.row (p i) x; refine ⟨fun z=>by positivity, ?_⟩; have hh x (hx:x∉Set.range U) : F x=0:= by unfold F; rw [outside p h _ _ hx]; simp
   have hy := (U.injective.hasSum_iff (a:=tsum G) hh).1 (by rw [← he]; exact hp.2.1.hasSum); exact ⟨hy.summable,hy.tsum_eq.le.trans hp.2.2⟩
lemma fans_sum [Fintype X] (F : Field ι X) (q : Field κ X) : ∑ x:κ→X, fans p F x * q x=∑ x:ι→X,F x*q (x∘ p):= by
  let U:= tube p h X; have he x (hx : x∉Set.range U): fans p F x*q x=0:= by rw [show fans p F x=0 from dif_neg (show ¬ x ∈Set.range (fun x:ι→X=> x∘ p) from hx),zero_mul];
  calc
     _= ∑' x:ι→X,fans p F (U x)*q (U x):= by rw [U.injective.tsum_eq (f:=fun x=>fans p F x*q x) (fun x hx=> by_contra fun hu=> hx (he x hu)), tsum_fintype]
     _= _:= by rw [tsum_fintype]; apply sum_congr rfl; intro x _; rw [show fans p F (U x)=_ from fans_read p h F x]; rfl
end
-- tap selection weights on parent labels
section
variable {f:Field ι (Node β)}
def faceCost (X:Type) (W: Field ι β)(F:Field ι (X×β)): Field ι (X×β) := fun i=> W (Prod.snd ∘ i) * F i
lemma faceCost_shape (h:Mirrored (backpack x) f) (W:Field ι β): Mirrored (backpack x) (faceCost Cover W f):= fun i=> congr_arg (W (Prod.snd ∘ i) * ·) (h i)
lemma faceCost_root {l:Pulse.Range (Node β)}  [Fintype β][Fintype ι] (H:Rooted l f b) (W: Field ι β): Rooted l (faceCost Cover W f) ((∑ i:ι→β, ‖W i‖)*b):= by
   let d:= ∑ i:ι→ β, ‖W i‖; have hd:0≤ d:=sum_nonneg (fun _ _=>by positivity); refine ⟨mul_nonneg hd H.cash, fun i y=> budget_mono (budget_scale hd (H.row i y)) (fun _=>by positivity) (fun q=>?_ )⟩; unfold faceCost; rw [norm_mul,mul_assoc]; gcongr; exact single_le_sum (fun i _=> norm_nonneg (W i)) (mem_univ _)
lemma faceCost_shadow (W:Field ι β){g: Field ι (Co m β)}(H: Shadow (lower m) f g): Shadow (lower m) (faceCost Cover W f) (faceCost (Site m) W g):= by
   intro i x y; have he:= H i x y; change faceCost _ _ _ _ =_; unfold faceCost; rw [show g y.val=_ from he, cram,cram,← tsum_mul_left]; apply tsum_congr; intro p; rw [show Prod.snd ∘ p.val.val= Prod.snd ∘ y.val from by rw (occs:=.pos [2]) [← p.property]; rfl]
end
end
end YM.Contacts.Barrage
