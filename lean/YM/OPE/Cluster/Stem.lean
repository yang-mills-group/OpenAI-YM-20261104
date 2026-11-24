import YM.OPE.Cluster.Order
/-!
# Composition projections along the retirement Mast
Cover geometry from chronological clustering, retained through sorted order even
when reaped together. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Finset Function Filter Set Lattice
open MergeProof Ribbons ManyCopies
open scoped Topology BigOperators Classical
variable {I J : Type}[Fintype I][DecidableEq I]
namespace Mast
variable (η:Mast I)
local notation "N"=> Fintype.card I
local notation "r"=> η.rank
local notation "P"=> η.parent
def depth (x:I):ℕ:= Fintype.card I - (η.rank x).val
lemma drops (x:I)(he:x ≠ η.root) : η.depth (η.parent x) < η.depth x:= Function.const _ (by
   have h: (r x).val<(r (P x)).val:= η.grows x he; have hz:(r (P x)).val<N:= (r (P x)).isLt; unfold depth; omega) (‹DecidableEq I›)
variable (u v:Finset I)
def trace (x:I): I:= if _h:x=η.root then x else if x∈u then x else trace (η.parent x)
termination_by η.depth x
decreasing_by exact η.drops _ _h
lemma same {x:I} (hx:x∈u):η.trace u x=x:=by rw [trace]; split_ifs <;> tauto
lemma follows {x:I} (h:η.root∈u)(he:x∉u): η.trace u x=η.trace u (η.parent x):=by rw [trace]; simp only [dif_neg (show x ≠ η.root from (fun e=>he (e.symm ▸ h))),if_neg he]
-- own all iterates from here
lemma travels (C:I→Prop) (h:C η.root) (he:∀ i,i ≠ η.root→ C (η.parent i) → C i) (i:I): C i:=by
   apply (InvImage.wf η.depth Nat.lt_wfRel.wf).induction (C:=C) i
   intro x IH; by_cases hx:x=η.root; exact hx.symm ▸ h; exact he x hx (IH _ (η.drops x hx))
lemma stands (he:η.root∈u)(x:I): η.trace u x∈u:=by
   refine η.travels (fun x=>η.trace u x∈u) (by rw [η.same _ he]; exact he) ?_ x; intro i hi hh;  by_cases h:i∈u; rw [η.same _ h]; exact h; rwa [η.follows _ he h]
def Region (η:Mast I)(p:Finset I) := ∀ i∈p,η.parent i∈p
lemma postpone {i:I} {x:I} (hx:x∈u)(he:η.Region u)(hs:η.trace v x=i)(h:η.root∈v): i∈u:=by
    suffices hv:∀ i∈u,η.trace v i∈u by rw [← hs]; exact hv _ hx
    apply η.travels; intro h'; rw [η.same _ h]; exact h'
    intro i hi hh hy; by_cases hp:i∈v; rw [η.same _ hp]; exact hy
    rw [η.follows _ h hp]; exact hh (he i hy)
lemma pipe (h: v ⊆ u)(he:η.root∈v)(x): η.trace v (η.trace u x)=η.trace v x:=by
   refine η.travels (fun x=>η.trace v (η.trace u x)=η.trace v x) ?_ ?_ x; rw [η.same u (h he)]
   intro i hi IH; by_cases hx:i∈u; rw [η.same _ hx]
   rw [η.follows u (h he) hx,IH,← η.follows v he (fun he=>hx (h he))]
variable (he:η.root∈v) (h:v⊆u)
def splice : Fibers u v:= ⟨fun x=> ⟨η.trace v x.val,η.stands _ he x.val⟩,fun x=> ⟨x.val,h x.property⟩,fun x=>Subtype.ext (η.same v x.property)⟩
lemma splice_val (x:u): ((η.splice u v he h).bunch x).val=η.trace v x.val:= rfl
lemma pipe_f (p:Finset I)(hp:p⊆v)(hs:η.root∈p): (η.splice u v he h).comp (η.splice v p hs hp)=η.splice u p hs (hp.trans h):=by
   have hh:(fun i: (u:Set I)=> η.trace p (η.trace v i.val))= fun i=> η.trace p i.val:=funext fun i=> η.pipe v p hp hs i
   unfold Fibers.comp splice; congr; funext x; exact Subtype.ext (η.pipe _ _ hp hs x.val) -- congr projections
lemma hits (q v:I)(he:η.root∈u)(hv:η.trace u q=v) (hz: q≠v)(p:Finset I)(hq:q∈p)(hP:η.Region p): ∃ w∈p,w∉u∧η.parent w=v:=by
   suffices h:∀ q∈p,η.trace u q=v → q≠v → _ by exact h q hq hv hz
   apply η.travels; swap
   · intro i hi H he' hq hv; have hp':i∉u:= fun hh=> hv ((η.same _ hh).symm.trans hq); by_cases hx:P i=v; exact ⟨i,he',hp',hx⟩; exact H (hP _ he') ((η.follows u he hp').symm.trans hq) hx
   intro h₁ h₂ h₃; rw [η.same u he] at h₂; contradiction
-- chart separation of surviving leaves: scalable bound based solely on ordered greedy inequality
def gate (n:ℕ): Finset I:= Finset.univ.filter (fun i=> n≤(r i).val)
-- variation indicator along axis of edge retirement.
def spark (z x:I) : Prop:= η.trace (η.gate (r z).val) x=z
def mask (z x:I): ℝ:= if η.spark z x then 1 else 0
lemma pulse {x:I}(h:x≠η.root)(z:I) : η.mask z x-η.mask z (η.parent x)=if z=x then 1 else 0:=by
   unfold mask spark; have hx(j:I)(a:I)(hq:(r j).val ≤ (r a).val):η.trace (η.gate (r j).val) a=a:= η.same _ (mem_filter.mpr ⟨mem_univ _,hq⟩)
   have hg:(r x).val<(r (P x)).val:= η.grows x h; by_cases hz:z=x; subst z; rw [hx _ _ le_rfl,hx _ _ hg.le,if_pos rfl,if_pos rfl, if_neg (show P x≠x from (fun he=> by rw [he] at hg; omega)),sub_zero]
   rw [if_neg hz]; by_cases hy:(r x).val<(r z).val; swap
   · have hv:(r z).val≤(r x).val:=le_of_not_gt hy; rw [hx _ _ hv,hx _ _ (hv.trans hg.le), if_neg (Ne.symm hz), if_neg (by intro he; rw [he] at hg; omega),sub_zero]
   rw [η.follows (x:=x) (η.gate _) (mem_filter.mpr ⟨mem_univ _,η.high z⟩) (fun hh=>(mem_filter.mp hh).2.not_gt hy),sub_self]
-- lemma when one is unrooted differences.Same-motion. Cost.
variable {E : Type*}[PseudoMetricSpace E](X:I→E)
lemma non (i:I):i∈η.gate (r i).val:= Function.const _ (mem_filter.mpr ⟨mem_univ _,le_rfl⟩) (‹DecidableEq I›)
lemma hierarchy (hp:η.Cluster (fun i j=> dist (X i) (X j)))(x y:I) (n:ℕ) (h:n ≤ (r η.root).val)
    (hx: η.trace (η.gate n) x ≠ η.trace (η.gate n) y) : dist (X (η.trace (η.gate n) x)) (X (η.trace (η.gate n) y)) ≤ (2:ℝ)^n * dist (X x) (X y):=by
   induction n with
   | zero=> have hh i:η.trace (η.gate 0) i=i:=η.same _ (mem_filter.mpr ⟨mem_univ _,Nat.zero_le _⟩); rw [hh,hh,pow_zero,one_mul]
   | succ i IH=>
      let v:= η.gate i; let u:=η.gate (i+1); let X':=η.trace v x; let Y':=η.trace v y
      have hh:u ⊆ v:= fun k hk=> mem_filter.mpr ⟨mem_univ _,i.le_succ.trans (mem_filter.mp hk).2⟩; have he:η.root∈u:=mem_filter.mpr ⟨mem_univ _,h⟩; have hx':η.trace u X'=η.trace u x:= η.pipe _ _ hh he x; have hy':η.trace u Y'=η.trace u y:= η.pipe _ _ hh he y
      have hn:X'≠Y':= fun ht=>hx (hx'.symm.trans ((congr_arg _ ht).trans hy'))
      have hV:= IH (i.le_succ.trans h) hn; rw [pow_succ',mul_assoc]; apply le_trans _ (mul_le_mul_of_nonneg_left hV zero_le_two)
      rw [← hx',← hy']; change dist (X (η.trace u X')) (X (η.trace u Y'))≤2*dist (X X') (X Y'); have hz:∀ i∈v,∀ j∈v,i≠j→i∉u → j∈u∧η.trace u i=P i ∧ dist (X i) (X (P i))≤dist (X i) (X j):=by
         have hO(x:I)(hp:x∈v)(he:x∉u): (r x).val=i:= by by_contra! he'; have hb:i ≤ (r x).val:= (mem_filter.mp hp).2; exact he (mem_filter.mpr ⟨mem_univ _,by omega⟩)
         intro i' h' j hq hn hz; have ho:= hO i' h' hz; have hw : i'≠ η.root:= fun HH=>hz (HH.symm ▸ he); have hg : (r i').val < (r (P i')).val:= η.grows i' hw
         exact ⟨Classical.byContradiction (fun ht=> hn (η.inj (Fin.ext (ho.trans (hO j hq ht).symm)))),(η.follows _ he hz).trans (η.same _ (mem_filter.mpr ⟨mem_univ _,by omega⟩)), hp.least i' hw j i' hn.symm (show (r i').val ≤ (r j).val from ho.symm ▸ (mem_filter.mp (show j∈v from hq)).2) le_rfl |>.trans_eq (dist_comm ..)⟩ -- need order hp.least
      have hX:X'∈v:=η.stands _ (hh he) x; have hY:Y'∈v:=η.stands _ (hh he) y; by_cases h1 : X'∈u
      · rw [η.same _ h1]; by_cases h2 : Y'∈u; rw [η.same _ h2]; exact le_mul_of_one_le_left dist_nonneg (by norm_num); obtain ⟨-,hq,hp⟩:=hz Y' hY X' hX hn.symm h2; rw [hq]; nth_rw 1 [dist_comm (X Y')] at hp; rw [dist_comm (X Y') (X X')] at hp; apply (dist_triangle (X X') (X Y') (X (P Y'))).trans; rw [dist_comm (X Y')]; linarith only [hp]
      obtain ⟨h1,h₂,h₃⟩:= hz X' hX Y' hY hn h1; rw [h₂,η.same _ h1]; exact (dist_triangle (X (P X')) (X X') (X Y')).trans (by rw [dist_comm (X (P X')) _]; linarith only [h₃])
end Mast
end YM.OPE.Yarn

