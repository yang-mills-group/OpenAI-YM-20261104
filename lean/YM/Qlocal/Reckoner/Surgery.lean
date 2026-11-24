import YM.Qlocal.Reckoner.Piling
/-!
# Preparing and using reassigned rows on their complete supports before stamp changes

Flags/tags and footprint predicates are fixed during all moves. All prices on Scribe rows themselves.
 In the application per-mode interaction forecasts and their compensating errors are new rows,
 not estimates on the old layout before payment. Here multiple surgeries can use same physical tags; keep individual marks through these changes.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories
variable {V Ω J J' J₀ K α:Type}[DecidableEq V]{G:Gauge}{n:Side}{R:Census V}
variable {X: RG.Rep G n}{s:V→ Support n}{q:Ray R} {A B t t':ℝ}
namespace Scribe
-- area of change, paid in p.union.Area at all earned maturity. Multiple rows per paired movement, include every old and new.
structure Loom (K:Type) (R:Census V)(n : Side) where
   region : K→Support n
   tag : K→R.Mode
   travel i : (region i).Nonempty
   not_blank i : (tag i).val.Nonempty
structure Lot (K:Type)(S:Scribe Ω J G n R)(L:Loom K R n) where
   rows : K→ Finset J
   singly (i j:K)(u:J)(hi:u∈rows i)(hj:u∈rows j): i=j
   logic (i:K)(u) (hi:u∈rows i) : S.tag u=L.tag i
   cost i u (hi:u∈rows i) : S.region u⊆ L.region i
variable (S:Scribe Ω J G n R) (T:Scribe Ω J' G n R) (p:BudgetPoint) (L:Loom K R n)
    (F:Lot K S L) (H:Lot K T L)
namespace Lot
variable {S T L}
abbrev runs (j:J) : Prop := ∃ i:K,j∈F.rows i
abbrev sought := eligible S F.runs
abbrev forget := eligible S (fun j=>¬F.runs j)
noncomputable def muses (x:Ω)(U:Config G n)(i:K):Poly R:=∑ j∈ F.rows i, S.enters p x U j
noncomputable def mint (x:Ω)(U:Config G n)(i:K):ℂ:=∑ j∈ F.rows i,S.render p x j U
-- Alternative condition at corner for equality only.Prop.Log.C.Sh.Support.Prim.We.Require.Area.Health
lemma spend_at (x U i): F.muses p x U i= Poly.send (L.tag i) (F.mint p x U i):=by
 unfold muses mint; let z:=Payload.send (L.tag i); change _= z _; rw [map_sum]; apply sum_congr rfl; intro j hj; unfold enters; rw [F.logic _ _ hj]; rfl
lemma credited (x U i)(hs: Healthy p.threshold (L.region i) U): F.mint p x U i=∑ j∈ F.rows i,S.score x j U:= by unfold mint; refine sum_congr rfl fun j hj=>?_; unfold render; split; rfl; exact masked_eq _ _ _ _ (Finset.disjoint_of_subset_left (F.cost i j hj) hs)
lemma luster (ha:Proper S p s)(x:Ω)(i:K): Parabola.Articles (L.region i) (fun U=> F.muses p x U i) s p.threshold:=by
 let g j U:= S.enters p x U j; have ht(h:Finset J)(hp:h⊆F.rows i): Parabola.Articles (L.region i) (∑ j∈h,g j) s p.threshold:=by
    induction h using Finset.induction with
    | empty=> rw [sum_empty]; exact Parabola.Articles.zero ..
    | insert a h hh ih=> rw [sum_insert hh]; exact ((ha.looks x a).enlarging (F.cost _ _ (hp (mem_insert_self ..)))).add (ih (Finset.Subset.trans (subset_insert ..) hp))
 rw [show (fun U=>F.muses p x U i)= ∑ j∈ F.rows i,g j from funext fun U=> (Finset.sum_apply U (F.rows i) g).symm]; exact ht _ (Finset.Subset.refl _)
variable [Fintype K]
lemma sent_recovery (x U): (F.sought).send p x U = ∑ i,F.muses p x U i := by
 let E:= Finset.biUnion Finset.univ F.rows; let f j:= S.enters p x U j; have hg i : i∈ E ↔ F.runs i:=by unfold E runs; simp
 unfold send; rw [tsum_eq_sum (s:=E)]; rotate_left
 · intro i hi; exact (Scribe.enters_off ..).trans (if_neg (mt (hg i).mpr hi)) -- implicit inferred?
 have h : Set.PairwiseDisjoint (↑(univ:Finset K): Set K) F.rows := fun i hi j hj h=>Finset.disjoint_left.mpr fun x hv=> fun he=> h (F.singly _ _ _ hv he)
 refine Eq.trans (b:=∑ j∈ E,f j) (sum_congr rfl ?_) (Finset.sum_biUnion h)
 exact fun i hi=> (Scribe.enters_off F.runs (x:=x) ..).trans (if_pos ((hg i).mp hi)) -- syntax

-- lot re-expression replacing all purchased, without changing any unsought row of S. Y unselected rows discarded.
noncomputable def turns := pile F.forget H.sought
noncomputable def leftover (x:Ω)(U:Config G n)(i:K):Poly R:= F.muses p x U i - H.muses p x U i
variable {p}
lemma turns_proper (ha:Proper S p s)(hb:Proper T p s): Proper (turns F H) p s:= (ha.eligible _).pile (hb.eligible _)
lemma turnout {ra rb:ℝ} (ug:S.Spend p q t ra)(vg:T.Spend p q t rb): (turns F H).Spend p q t (ra+rb):= (ug.eligible (fun j=>¬ F.runs j)).pile (vg.eligible _)
include F H
local notation "Q"=> F.turns H
variable (p)
lemma exact_at (ha: S.Proper p s)(hb:T.Proper p s)(hu:S.Spend p q t A)(hv:T.Spend p q t B)(hr:Rental q)(ht:0≤t)(x v): S.send p x v = (Q).send p x v+ ∑ i:K,leftover p F H x v i:= by
 have hf:= pool (ha.eligible (fun j=>¬ F.runs j)) (hb.eligible H.runs) (hu.eligible _) (hv.eligible _) hr ht x v -- arguments? window
 rw [show S.send p x v=F.sought.send p x v+F.forget.send p x v from (split_Book (F.runs) ha hu hr ht x v), F.sent_recovery]; rw [show (Q).send p x v= _ from (show _=F.forget.send p x v+ H.sought.send p x v from hf),H.sent_recovery]; unfold leftover; simp only [sum_sub_distrib]; abel
-- edit manually
lemma splits (ha:S.Proper p s)(hb:T.Proper p s)(x i): Parabola.Articles (L.region i) (fun U=>F.leftover p H x U i) s p.threshold:=by
 let f U:= H.muses p x U i; have ht:= H.luster p hb x i
 suffices h: Parabola.Articles (L.region i) (-f) s p.threshold by simp_rw [leftover,sub_eq_add_neg]; exact (F.luster p ha x i|>.add h)
 refine ⟨fun U V he hv=> congr_arg (-·) (ht.travel _ _ he hv), fun j=> Measurable.neg (ht.visible j),fun g U=>congr_arg (-·) (ht.worth _ _),fun U v hv=> ht.owns U v (fun h=> hv (by change - (H.muses p x U i).part _=0; rw [h]; exact neg_zero))⟩
lemma arc (x v i): F.leftover p H x v i= Poly.send (L.tag i) (F.mint p x v i-H.mint p x v i):= by
 unfold leftover; rw [F.spend_at,H.spend_at]; exact (map_sub (Payload.send (L.tag i)) ..).symm
variable (hm:∀ i x U, Healthy p.threshold (L.region i) U → ∑ j∈F.rows i,S.score x j U=∑ j∈ H.rows i,T.score x j U)
-- embedding.Need all V Fintype in pass.
def tents (L:Loom K R n) : Corrections G n where
  region:= unpin L.region {(0:Site n)}
  value:=0
set_option quotPrecheck false
local notation "Xv"=> Lot.tents L
noncomputable def ink (x:Ω)(j:ℕ) (U:Config G n):= unpin (F.leftover p H x U) 0 j -- arg α
lemma ink_code (x i U): ink p F H x (pin i) U=F.leftover p H x U i:=by unfold ink; rw [unpin_pin]
lemma unhook (x U): ∑' i:ℕ,ink p F H x i U= ∑ i:K,leftover p F H x U i:= by
 rw [show ∑ i:K, leftover p F H x U i = ∑' i:K, leftover p F H x U i from (tsum_fintype _).symm]; refine (Push.Corrected.Pad.sums _ pin_injective _ _ (fun i=>ink_code ..) ?_).symm -- push
 · intro i hi; by_contra hz; exact hi (unpin_blank _ _ hz)
lemma extension_ (i:K): ((Lot.tents L:Corrections G n)).region (pin i)= L.region i:= by unfold Lot.tents; dsimp only; rw [unpin_pin]
include hm
lemma parking [Fintype V] (ha:S.Proper p s)(hb:T.Proper p s)(hu:S.Spend p q t A)(hv:T.Spend p q t B)(hr:Rental q)(ht:0≤t)(x:Ω): Changes p (Lot.tents L) (S.send p x) ((Q).send p x) (ink p F H x) s:=by
 have hP i : ink p F H x (pin i)=fun U=>F.leftover p H x U i:=funext fun U=> ink_code ..
 have he i (hi:i∉Set.range (pin:K→ℕ)): ink p F H x i=0:= funext fun U=> unpin_blank _ _ hi
 refine ⟨fun i=> ?_,fun i U=> ?_,fun i U=>?_,fun i U=> ?_,fun U=> ?_,fun U=> calm_send (F.turnout H hu hv) hr (F.turns_proper H ha hb) ht x U⟩ -- binder hm etc implicit
 · by_cases hb2:i∈Set.range (pin:K→ℕ); swap; · rw [he _ hb2]; exact Parabola.Articles.zero ..
   obtain ⟨i,rfl⟩:=hb2; rw [extension_ (F:=F) (H:=H), hP]; exact Lot.splits p F H ha hb x i
 · by_cases hy:i ∈ Set.range (pin:K→ℕ); swap; · rw [he _ hy]; rfl
   obtain ⟨i,rfl⟩:=hy; rw [ink_code,leftover,sub_eq_add_neg,Poly.part_plus,Poly.part_neg,F.spend_at,H.spend_at,Poly.part_send,Poly.part_send]; split; next hc=> exact False.elim ((L.not_blank i).ne_empty (congr_arg Subtype.val hc.symm))
   next=> simp
 · by_cases hb:i∈Set.range (pin:K→ℕ); swap; · rw [he _ hb]; exact fun _=>rfl
   obtain ⟨i,rfl⟩:=hb; rw [extension_ (F:=F) (H:=H),ink_code,arc]; intro hz; rw [credited _ _ _ _ _ hz,credited _ _ _ _ _ hz,hm _ _ _ hz,sub_self,Poly.send_zero]
 · by_cases hb:i∈Set.range (pin:K→ℕ); swap; · rw [he _ hb, Pi.zero_apply, Extra.Trajectories.pass_zero, add_zero] -- edit
   obtain ⟨i,rfl⟩:=hb; rw [ink_code,arc, Extra.Trajectories.pass_send (L.not_blank i) _]
 rw [unhook]; exact exact_at p F H ha hb hu hv hr ht x U
end Lot
end Scribe
end YM.Qlocal.Reckoner
