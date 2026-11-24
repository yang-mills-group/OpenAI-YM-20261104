import YM.OPE.Compatible.Dale.Mont
/-!
# Combining stands at the single remote joint check
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory
open scoped Topology BigOperators ComplexConjugate Classical
namespace Score
variable {D W V J:Type*}(T:Score D V)(R:Score W J)
-- D first, W second meaning virtual coarse pilots
def tie (q:J→V): Score (D ⊕ W) V:=⟨Sum.elim T.inn (q∘R.inn),Sum.elim T.out (q∘ R.out)⟩
def early (p:D×Bool): (D⊕W) × Bool:=(Sum.inl p.1,p.2)
def late (p:W × Bool):(D⊕W) × Bool:=(Sum.inr p.1,p.2)
@[simp] lemma eStart (p:D× Bool)(q:J→V): (T.tie R q).start (early p)=T.start p:=by simp only [start,early,tie,Sum.elim_inl]
@[simp] lemma eLast (p:D× Bool)(q:J→V): (T.tie R q).lastV (early p)=T.lastV p:=by simp only [lastV,early,tie,Sum.elim_inl]
@[simp] lemma lStart (p:W× Bool)(q:J→V): (T.tie R q).start (late p)=q (R.start p):=by simp only [start,late,tie,Sum.elim_inr,comp_apply]; split <;>rfl
@[simp] lemma lLast (p:W× Bool)(q:J→V): (T.tie R q).lastV (late p)=q (R.lastV p):=by simp only [lastV,late,tie,Sum.elim_inr,comp_apply]; split <;>rfl
namespace Stand
variable {T}
variable {B:Set V} (A:T.Stand B)
def Slotting (q:J→V): (T.tie R q).Stand B where
    point i:=early (A.point i)
    root i:= (eStart ..).trans (A.root i)
    flick :=A.flick
    bump i:=by rw [eLast]; exact A.bump i
lemma slotted (q:J→V)(x:D): (A.Slotting R q).Branch (Sum.inl x) ↔ A.Branch x:=by
       unfold Branch Slotting early; simp only [mem_range,comp_apply,Sum.inl.injEq]
lemma unslotted (q:J→V)(x:W): ¬ (A.Slotting R q).Branch (Sum.inr x):=by simp [Branch,Slotting,early]
omit A
variable {R}{q:J→V}{u:V→J}{L:Set J}
variable (Q:R.Stand L) (A:T.Stand (Set.range q)) (h: LeftInverse u q)(G:∀ i: ↥((Set.range q)ᶜ), u (T.lastV (A.point i))=u i.val)(m:ℕ)(H:∀ i,A.flick i<m)
private lemma raiseR (i:V)(hi:i∈ Set.range q): LeftInverse u q→q (u i)=i:=by rintro h; obtain ⟨j,rfl⟩:=hi; rw [h]
private lemma layer (i: ↥((q '' L)ᶜ))(hi:i.val ∈ Set.range q): LeftInverse u q→u i.val∈ Lᶜ:=by intro h hj; exact i.property ⟨u i.val,hj,raiseR i.val hi h⟩ -- type compl fix
include h
def raft (i: ↥((q '' L)ᶜ)) : (D ⊕ W) × Bool:= if v: i.val∈ (Set.range q)ᶜ then early (A.point ⟨i.val,v⟩) else
    late (Q.point ⟨u i.val,layer i (not_not.mp v) h⟩)
def tieIn (G:∀ i: ↥((Set.range q)ᶜ), u (T.lastV (A.point i))=u i.val)(m:ℕ)(H:∀ i,A.flick i<m): (T.tie R q).Stand (q '' L) where
   point:=Q.raft A h
   flick i:= m*Q.flick (u i)+ A.flick i
   root i:=by unfold raft; split
              next v=> rw [eStart,A.root]
              next v=> rw [lStart,Q.root]; exact raiseR _ (not_not.mp v) h
   bump i:=by unfold raft; split
              next v=> rw [eLast,G]; exact Nat.add_lt_add_left (A.bump ⟨i.val,v⟩) _
              next v=> rw [lLast,h]; let p:= Q.point ⟨u i.val,layer i (not_not.mp v) h⟩; have hs: Q.flick (R.lastV p)<Q.flick (u i.val):= Q.bump _; apply lt_of_lt_of_le (b:= m*Q.flick (R.lastV p)+m) (Nat.add_lt_add_left (H _) _); rw [← Nat.mul_succ]; exact (Nat.mul_le_mul_left m (show Q.flick _+1 ≤ _ from hs)).trans (Nat.le_add_right ..)
include H G
lemma coversD (x:D): (tieIn Q A h G m H).Branch (Sum.inl x) ↔ A.Branch x:=by
    constructor
    · rintro ⟨i,hi⟩; change (Q.raft A h i).1=_ at hi; unfold raft at hi; split at hi <;> rename_i v
      · exact ⟨⟨_,v⟩,Sum.inl.inj hi⟩
      simp [late] at hi
    rintro ⟨i,hi⟩; have hv:i.val ∈ (q '' L)ᶜ:=fun ⟨p,_,hp⟩=> i.property ⟨p,hp⟩
    refine ⟨⟨_,hv⟩,?_⟩; change (Q.raft A h ⟨i.val,hv⟩).1=_; unfold raft; rw [dif_pos i.property]; exact congr_arg (Sum.inl (β:=W)) hi
lemma coversW (x:W): (tieIn Q A h G m H).Branch (Sum.inr x) ↔ Q.Branch x:=by
     constructor
     · rintro ⟨i,hi⟩; change (Q.raft A h i).1=_ at hi; unfold raft at hi; split at hi <;> rename_i v
       · simp [early] at hi
       exact ⟨_, Sum.inr.inj hi⟩
     rintro ⟨i,hi⟩; have hv:q i.val ∈ (q '' L)ᶜ:=fun ⟨p,hp,hq⟩=> i.property ((h.injective hq) ▸ hp)
     have hl: q i.val∉ (Set.range q)ᶜ:= not_not.mpr ⟨_,rfl⟩
     refine ⟨⟨_,hv⟩,?_⟩; change (Q.raft A h ⟨q i.val,hv⟩).1=_; unfold raft; rw [dif_neg hl,show ∀ hh, (⟨u (Subtype.val _) ,hh⟩:↥(Lᶜ))=i from fun hh=>Subtype.ext (h _)] -- wrong
     exact congr_arg (Sum.inr (α:=D)) hi
end Stand
end Score
end YM.OPE.Cascade
