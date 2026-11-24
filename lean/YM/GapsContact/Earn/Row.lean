import YM.GapsContact.Earn.Clime
/-!
# Uniform payments for spectators and inner extensions of route receipts

Use SAME peal/spelling as Frontier6's extending systematic (Tale). Applies with centroids,
tomography tests translated away from them, honors Real (this prescription RealSpin etc retained),
and in every chamber. Test-unit lengths g ≤ η and opposite-side separate widths, not shape-compact.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open Function Filter Set MeasureTheory Analysis Ward Spec Table Extraction Lattice
open Frontier6 Frontier6.Tale OPE Trace Trace.Pilot Ascent Power
open scoped Topology BigOperators ContDiff InnerProductSpace Classical
variable {I J:Type*}[Fintype I][Fintype J]
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S){hG:G.Simple} {A:EveryPhase.Almanac F}
universe u
variable (H:Roll.{u} F hG A)
variable (d:I→ℕ)(e:J→ℕ)
variable {t r a ε g:ℝ}{o:E4}
variable {x:I→ E4}{y:J→ E4}
local notation "U!"=> F.room.kernel
local notation "E!"=> F.sector.derivatives
local notation "↑̂"=> Work.C01.center -- remove

/-- cost characters/file sets of peal. -/
abbrev crestSet (c:I→ℝ) (v: I→ S.Tag) :ℝ:= ∏ i,cost F (v i).1 (c i) (v i).2
abbrev billSlots (g:ℝ) (v: I→ S.Tag) :ℝ:= crestSet F (fun _=>g) v
lemma billSlots_pos (x:ℝ)(v:I→ S.Tag):0 ≤ billSlots F x v:= Finset.prod_nonneg (fun _ _=>Ascent.cost_pos ..)
abbrev chargeSet (c:ℝ)(v:∀i,S.Field (d i)):= billSlots F c (fun i=>⟨d i,v i⟩)
include H
lemma acrossCorners {s:ℝ}(hp:0<s) : ∃ (B:ℝ)(m:ℕ),1≤B ∧ ∀ (g:ℝ) (_hg:g∈Ioc 0 1) (r:I→ℝ)(_hr:∀ i,r i∈ Icc g 1)(x:I→ E4), Pairwise (fun i j=> s*r i≤ ‖x i-x j‖) →
    ∀ (p:StateIndex F)(v:I→ S.Tag), (∀ i,(v i).1=d i) → ‖peal F p (assembly S x v)‖ ≤ B*dock g^m * crestSet F r v:=by
   let U:= (Fintype.equivFin I).symm
   obtain ⟨B,m,hB,hT⟩:= beach_all F H (d ∘ U) hp; refine ⟨B,m,hB,fun g hg r hr x hA p v hv=>?_⟩
   have hx: Injective x:=by intro i j hi; by_contra! hQ; have he := (mul_pos hp (hg.1.trans_le (hr i).1)).trans_le (hA hQ); rw [hi,sub_self,norm_zero] at he; exact lt_irrefl _ he
   have he(i):∃ u:S.Field (d i), v i=(⟨d i,u⟩:S.Tag):=by rw [← hv i]; exact ⟨_,rfl⟩
   choose u hU using he; rw [show v=(fun i=> (⟨d i,u i⟩: S.Tag)) from funext hU]
   unfold peal; rw [acast F p,if_pos hx, show state F p= Survey.table (F:=F) p from (by cases p<;>rfl)]
   refine (hT g hg (points (x ∘ U)) (r ∘ U) (fun i=>hr _) (fun i j h => hA (U.injective.ne h)) p (fun i=> u (U i))).trans_eq ?_; exact congr_arg (fun A:ℝ=> B*dock g^m * A) (Equiv.prod_comp U (fun i=> cost F (d i) (r i) (u i)))

omit H
section
omit [Fintype I] [Fintype J]
structure Shelf (g r t : ℝ) : Prop where
   credit : 0<g
   fit : g ≤ r
   cut : 8*r ≤ t
   stop : t ≤ 1
lemma Shelf.tie (h:Shelf g r t): g ≤ r ∧ r ≤ t:= ⟨h.fit, by linarith only [h.credit,h.fit,h.cut]⟩
lemma Shelf.period (h:Shelf g r t):0<g∧0<r∧t∈ Ioc (0:ℝ) 1:= ⟨h.credit,h.credit.trans_le h.fit,h.credit.trans_le (h.fit.trans h.tie.2),h.stop⟩

/-- input arity, without radial cutoff yet. Named. Two layers normal and dilated 1/2--2 for stencil reads. -/
structure InsideS (g r:ℝ)(x:I→ E4)(o:E4) : Prop where
   admits : ∀ i,‖x i-o‖ ≤ r
   shares : Pairwise (fun i j=> g ≤ ‖x i-x j‖)
lemma InsideS.enlarge {g' r':ℝ}(h:InsideS g r x o)(hp:g'≤g)(hr:r≤r') : InsideS g' r' x o:=⟨fun i=> (h.admits i).trans hr, fun _ _ he=> hp.trans (h.shares he)⟩
abbrev VisitS (g r:ℝ)(x:I→ E4)(o:E4):Prop:= InsideS (g/2) (2*r) x o
lemma InsideS.visit (hz:Shelf g r t)(h:InsideS g r x o) : VisitS g r x o:=h.enlarge (half_lt_self hz.credit|>.le) (by linarith only [hz.period.2.1])

/-- including centroid in interior and all others outside aperture; proper collision patches recover full shell. -/
structure Balcony (g a t:ℝ)(y:J→ E4)(o:E4) : Prop where
   spot : g≤a
   horizon : a≤ t
   outside : ∀ i,t ≤ ‖y i-o‖
   ways : Pairwise (fun i j=> a ≤ ‖y i-y j‖)

-- uses cross charge law independently each width (and after merging).
lemma keepDesk (x:I→ E4)(p:I→ℝ)(hh:∀ i,0<p i)(he:Pairwise (fun i j=> p i≤ ‖x i-x j‖)):Injective x:=by intro i j hi; by_contra! hk; have ht:=(hh i).trans_le (he hk); rw [hi,sub_self,norm_zero] at ht; exact lt_irrefl _ ht
namespace Balcony
variable (ha:Balcony g a t y o) (hx:VisitS g r x o)(hr:Shelf g r t)
include ha
lemma shot:g ≤ a ∧ a ≤ t:=⟨ha.spot,ha.horizon⟩ -- hd unused p
lemma lower {s:ℝ}(h:s ≤ t)(hp:a ≤ s): Balcony g a s y o:= ⟨ha.spot,hp,fun i=> h.trans (ha.outside i),ha.ways⟩ -- s unknown!
include hx hr
lemma joins : Pairwise (fun i j=> (1/2:ℝ) * beside (fun _:I=>g) (fun _:J=> a) i ≤ ‖beside x y i-beside x y j‖):=by
   have hv:g ≤ a:=ha.spot; have h:g∈ Ioc 0 1:= ⟨hr.credit,(ha.spot.trans ha.horizon).trans hr.stop⟩; have he(i:I)(j:J) : (1/2:ℝ)* a ≤ ‖x i-y j‖:=by have he:= norm_sub_norm_le (y j-o) (x i-o); rw [sub_sub_sub_cancel_right,norm_sub_rev (y j) (x i)] at he; linarith only [ha.horizon,ha.outside j, hx.admits i,hr.cut,hr.period.2.2.1,he]
   rintro (i|i) (j|j) hX
   · change (1/2:ℝ)*g≤_; have hu:i≠j:= fun h=> hX (congr_arg _ h);
     rw [show (1/2:ℝ)*g=g/2 from (by ring)]; exact hx.shares hu
   · exact (mul_le_mul_of_nonneg_left ha.spot (by norm_num : (0:ℝ)≤1/2)).trans (he i j)
   · exact (he j i).trans_eq (norm_sub_rev ..)
   have hu:i ≠ j:=fun h=> hX (congr_arg _ h); exact le_trans (mul_le_of_le_one_left (le_trans hr.credit.le hv) (by norm_num : (1/2:ℝ)≤1)) (ha.ways hu)
lemma join_live : Injective (beside x y):=keepDesk _ _ (by rintro (i|i); exact mul_pos (by norm_num : (0:ℝ)<1/2) hr.credit; exact mul_pos (by norm_num : (0:ℝ)<1/2) (lt_of_lt_of_le hr.credit ha.spot)) (ha.joins hx hr) -- order
omit hx hr
lemma lands (hg: 0< g) : Pairwise (fun i j=> (1/2:ℝ) * beside (fun _:Unit=>t) (fun _:J=>a) i ≤ ‖beside (fun _:Unit=>o) y i-beside (fun _:Unit=>o) y j‖):=by
   have h:g ≤ a:=ha.spot; have hp :g ≤ t:= ha.spot.trans ha.horizon; rintro (i|i) (j|j) hX
   · exact (hX (by congr 1)).elim
   · exact ((mul_le_of_le_one_left (hg.le.trans hp) (by norm_num : (1/2:ℝ)≤1)).trans (ha.outside j)).trans_eq (norm_sub_rev ..)
   · exact (mul_le_of_le_one_left (hg.le.trans h) (by norm_num : (1/2:ℝ)≤1)).trans (ha.horizon.trans (ha.outside i))
   have hu:i≠j:= fun h=> hX (congr_arg _ h); exact (mul_le_of_le_one_left (hg.le.trans h) (by norm_num : (1/2:ℝ)≤1)).trans (ha.ways hu)
end Balcony

end
include H
lemma raw_slots : ∃ (B:ℝ)(m:ℕ),1 ≤ B ∧ ∀ (o:E4)(p:StateIndex F) (g r t a:ℝ) (x:I→ E4)(y:J→ E4)(v:I→ S.Tag)(u:J→ S.Tag), Shelf g r t→VisitS g r x o → Balcony g a t y o → (∀ i,(v i).1=d i) → (∀ i,(u i).1=e i) →
    ‖peal F p (assembly S x v * assembly S y u)‖ ≤ B*dock g^m * billSlots F g v * billSlots F a u:=by
   obtain ⟨B,m,hB,hV⟩:= acrossCorners F H (beside d e) (by norm_num:(0:ℝ)<1/2)
   refine ⟨B,m,hB,fun o p g r t a x y v u h hX hY he hf=>?_⟩; rw [← Tale.concatenates]
   let s:= beside (fun _ : I=> g) (fun _ : J=>a)
   have ht:g∈ Ioc (0:ℝ) 1:=⟨h.credit,(hY.spot.trans hY.horizon).trans h.stop⟩
   have hp(i): s i∈ Icc g 1:=by cases i; exact ⟨le_rfl,ht.2⟩; exact ⟨hY.spot,hY.horizon.trans h.stop⟩
   apply (hV g ht s hp _ (hY.joins hX h) p (beside v u) (by rintro (i|i); exact he i; exact hf i)).trans_eq
   unfold crestSet; rw [Fintype.prod_sum_type, mul_assoc (_*_)] -- likely mul_assoc many
   rfl
lemma raw_letter (d:ℕ) : ∃ (B:ℝ)(m:ℕ),1≤B∧ ∀ (o:E4)(p:StateIndex F) (g t a:ℝ) (y:J→ E4)(x:S.Field d)(v:J→ S.Tag), t≤1→ 0<g→ Balcony g a t y o→ (∀ i,(v i).1=e i) →
    ‖peal F p (letter S o ⟨d,x⟩ * assembly S y v)‖ ≤ B*dock g^m * cost F d t x * billSlots F a v:=by
   obtain ⟨B,m,hB,hV⟩:= acrossCorners F H (beside (fun _:Unit=>d) e) (by norm_num : (0:ℝ)<1/2); refine ⟨B,m,hB,fun o p g t a y x v ht hg ha hv=>?_⟩
   let W:= beside (fun _ : Unit=>t) (fun _ : J=>a); let V':= fun _ : Unit=> (⟨d,x⟩:S.Tag)
   have h:g∈ Ioc (0:ℝ) 1:=⟨hg,(ha.spot.trans ha.horizon).trans ht⟩; have hp(i): W i∈ Icc g 1:=by cases i; exact ⟨ha.spot.trans ha.horizon, ht⟩; exact ⟨ha.spot,ha.horizon.trans ht⟩
   rw [show letter S o ⟨d,x⟩= assembly S (fun _ : Unit=>o) V' from by rw [assembly, Fintype.prod_unique], ← Tale.concatenates]
   apply (hV g h W hp _ (ha.lands hg) p (beside V' v) (by rintro (i|i); rfl; exact hv i)).trans_eq
   unfold crestSet; rw [Fintype.prod_sum_type,Fintype.prod_unique, mul_assoc (_*_)];rfl
end YM.GapsContact.Seams
