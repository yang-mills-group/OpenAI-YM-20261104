import YM.OPE.Compatible.Lines.Compass
/-!
# Hierarchically controlled coordinate moves. Use relative offsets in axis basis of the current frame. Even offsets as coarse as the root don't translate relative interior of deeper tiers. Oversampled grid chosen after all lengths. Station coordinates align exactly through cutoff and volume projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice
open scoped Topology BigOperators Classical
variable {X:Type} [PartialOrder X][OrderBot X][Fintype X]
variable (D:Origin X) (Q:Finset X) (h:Crown Q)
variable {G:Gauge}{C:Family G}{J:Set X}
def legs := (allUp D Q).erase ⊥
-- Induces translations on branched names
abbrev Wing : Type := legs D Q × Axis
-- simpler abbrev? syntax allowed `def` deriving Product?
set_option quotPrecheck false
local notation "P!"=> Wing D Q
variable (s:X→ℝ)(a : Sight) (x:X→E4)(f:Wing D Q→ℝ)
local notation "fer"=>fun w:P!=> par D w.fst.val
local notation "k"=>fun w:P!=> FrameRead.trail (a.code w.snd)
-- explicit translation-onset
def inMotion (x:P!)(v:X) : Prop:= x.fst.val ≤ v
-- note param D Q explicit
def displacement (v:X): E4:=∑ i:P!, if inMotion D Q i v then (f i * s (fer i)) • (FrameRead.trail (a.code i.snd)) else 0
def reload (v:X) := x v+ displacement D Q s a f v
lemma reload_base : reload D Q s a x (fun _=>0)=x:=by ext1 j; simp [reload,displacement]
lemma belly : reload D Q s a x f ⊥ = x ⊥:=by
   unfold reload; apply add_eq_left.mpr; unfold displacement; apply Finset.sum_eq_zero; intro i _; exact if_neg (fun h:inMotion D Q i ⊥=> ((Finset.mem_erase.mp i.fst.2).1 (le_bot_iff.mp h)))
-- for one direction across this coordinate
lemma differential (v:X)(j:P!)(t:ℝ) : reload D Q s a x (Function.update f j t) v = reload D Q s a x (Function.update f j 0) v + (t*(if inMotion D Q j v then s (fer j) else 0)) • FrameRead.trail (a.code j.2):=by
   unfold reload displacement; rw [add_assoc]; congr 1
   let F (i:P!)(f:Wing D Q→ℝ): E4:= if inMotion D Q i v then (f i *s (fer i)) • FrameRead.trail (a.code i.snd) else 0
   have h(u:ℝ): (∑ i,F i (Function.update f j u))=(∑ i ∈ Finset.univ.erase j,F i f)+F j (Function.update f j u):=by rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]; congr 1; apply Finset.sum_congr rfl; intro i he; simp_rw [F,Function.update_of_ne ((Finset.mem_erase.mp he).1)]
   change (∑ i,F i (Function.update f j t))= (∑ i,F i (Function.update f j 0))+_; rw [h,h]; by_cases hp : inMotion D Q j v <;> simp [F,hp]
include h
lemma par_leg {i:X}(hi:i∈allUp D Q):par D i∈ Q := by
    rcases Finset.mem_union.mp hi with hy|hy; exact h.roots (par_le ..) hy; exact ((on_brim ..).mp hy).2.2
omit h
-- normalization of path
private def fluid (L:(i:P!)→ ℝ) (v : legs D Q):=∑ j:Axis,(L (v,j)*s (par D v.val)) • FrameRead.trail (a.code j)
lemma step_reload (v:legs D Q) : reload D Q s a x f v.val -reload D Q s a x f (par D v.val) = x v.val-x (par D v.val)+fluid D Q s a f v:=by
    unfold reload displacement; simp_rw [Fintype.sum_prod_type]; let F (i:legs D Q):=fluid D Q s a f i; let m(v:X)(i:legs D Q): E4:=∑ j:Axis, if inMotion D Q (i,j) v then (f (i,j)*s (par D i.val)) • FrameRead.trail (a.code j) else 0
    have ht(i):m v.val i-m (par D v.val) i= if i=v then F v else 0:=by
        have hx:= from_par D ((Finset.mem_erase.mp v.2).1); unfold m; simp only [inMotion]; by_cases hp : i=v; subst i; · rw [if_pos rfl]; simp [hx.not_ge,F,fluid]
        rw [if_neg hp]; have hh : (i.val ≤ v.val)↔ i.val≤ par D v.val:= ⟨fun hh=> touch_par D (hh.lt_of_ne (Subtype.val_injective.ne hp)), fun hh=>hh.trans hx.le⟩; simp only [hh]; exact sub_self _
    have hc: (∑ i,m v.val i)-(∑ i,m (par D v.val) i)=F v:=by rw [← Finset.sum_sub_distrib]; simp_rw [ht]; simp
    change x v.val + (∑ i,m v.val i)-(x (par D v.val) + ∑ i,m (par D v.val) i)=_+F v; rw [← hc]; abel
-- representation at edge speeds. residual after updating all slots
lemma coordinates : ∃ w:P!→ℝ, ∀ j:legs D Q,x j-x (par D j)=∑ i:Axis,w (j,i) • FrameRead.trail (a.code i):=by
    choose f hf using fun j:legs D Q=> sees_across a (x j-x (par D j)); exact ⟨fun x=>f x.fst x.snd,fun _=>(hf _).symm⟩
-- if conforming variables, placement at lattice grid
variable {m:X→ℕ}(w:Wing D Q→ℝ)
def Frozen (i:P!): Prop:=∃ b:ℤ, w i + f i * s (fer i) = C.S.a (m i.fst.val)* (b:ℝ)
include h
lemma frost (hx:x ⊥=0)(hp:∀ j:legs D Q,x j-x (par D j)=∑ i:Axis,w (j,i) • FrameRead.trail (a.code i)) (hm:∀ i∈legs D Q, m (par D i) ≤ m i)(hW:∀ i:P!,Frozen D Q s f (C:=C) w (m:=m) i) : ∀ i∈ allUp D Q, ∃ k':Cover, C.S.gridPoint (m i) k'=reload D Q s a x f i:=by
   refine fun i=> journey D (P:=fun i=> i∈allUp D Q→∃ k':Cover,C.S.gridPoint (m i) k'=reload D Q s a x f i ) (fun hm=> ?_) ?_ i
   · exact ⟨0,by rw [belly,hx,grid_zero]⟩
   intro i hi ih hq; obtain ⟨j,hj⟩:= ih (Finset.mem_union_left _ (par_leg D Q h hq)); let v : legs D Q:=⟨i,Finset.mem_erase.mpr ⟨hi,hq⟩⟩; let H:=hm i v.2; let K:= OPE.zoom C.S H j; let t e:= w (v,e)+f (v,e)*s (par D v)
   have he(u u'): C.S.gridPoint (m i) (u+u')=C.S.gridPoint (m i) u+C.S.gridPoint (m i) u':=by ext c; simp [Schedule.gridPoint]; ring
   have hy(e): ∃ l:Cover,C.S.gridPoint (m i) l=t e • FrameRead.trail (a.code e):=by obtain ⟨z,hz⟩:= hW (v,e); unfold t; rw [hz]; exact trail_step ..
   choose l hl using hy; refine ⟨(∑ e,l e)+K,?_⟩; rw [he,show C.S.gridPoint (m i) K= _ from (zoom_grid H _).trans hj,← eq_sub_iff_add_eq];
   rw [show reload D Q s a x f i -_= _ from step_reload D Q s a x f v,hp v]; unfold fluid; rw [← Finset.sum_add_distrib]; let L :Cover →+ E4:={ toFun:=C.S.gridPoint (m i),map_add' := he,map_zero' :=grid_zero ..}
   change L (∑ e,l e)=_; rw [map_sum]; refine Finset.sum_congr rfl fun e _=>?_ ; change C.S.gridPoint _ (l e)=_; rw [hl]; unfold t; rw [add_smul]
end YM.OPE.Arboreal.Trace
