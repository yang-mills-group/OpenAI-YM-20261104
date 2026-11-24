import YM.OPE.Measuring.Paths

/-!
# Trimming literal unit channels from a common quantitative prescription

Only use the unit slot identity on its genuinely separated detector domain.
Needed both inside the Reader and when evaluating the resulting field in a
phase. Tag is typed by the original filtered field throughout. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sparse
open YM.OPE.Nesting Orbits Orbits.Reader Function Filter Extraction Set Table Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)

abbrev literal (v:S.Tag):Prop:= v.snd = S.unit v.fst

namespace Undo
variable {I J:Type}[Fintype I][Fintype J]

def MarginType:= (I:Type)→(I→E4)→Prop
abbrev Kernel (S:Table C.book)(B:Type):=∀ (I:Type)[c:Fintype I],(I→E4)→(I→S.Tag)→ B
abbrev apply {B:Type}(K:Kernel S B)(x:I→E4)(v:I→S.Tag) :=K I x v
-- Laws that suffice for arbitrary families of unit deletions
structure Identity (S:Table C.book)(B:Type)(Q:MarginType)(p:Kernel S B): Prop where
  shrink: ∀ (I J:Type)(x:I→E4)(e:J→I), Q I x → Injective e → Q J (x ∘ e)
  perm: ∀ (I J:Type)[Fintype I][Fintype J](e:J≃I)(x:I→E4)(v:I→S.Tag), Q I x → apply p x v= apply p (x ∘ e) (v ∘ e)
  erase: ∀ (I:Type)[Fintype I] (x:I→E4)(o:E4)(i:ℕ)(v:I→S.Tag),Q (Unit⊕I) (beside (sole o) x) → apply p (beside (sole o) x) (beside (sole (⟨i,S.unit i⟩:S.Tag)) v) = apply p x v

variable {Q:MarginType}{B:Type}{p:Kernel S B}(hp: Identity S B Q p)

private def adjoin {i:I}{q:Finset I} (h:i∉q): Unit⊕↑q ≃ ↑(insert i q) where
  toFun
    | .inl _ => ⟨i,mem_insert_self ..⟩
    | .inr ⟨j,h⟩ => ⟨j,mem_insert_of_mem h⟩
  invFun v :=if hv: (v.val:I)=i then Sum.inl () else Sum.inr ⟨v.val,mem_of_mem_insert_of_ne v.property hv⟩
  left_inv:= fun v=>by
     rcases v with ⟨_⟩ | ⟨j,hj⟩
     · simp
     · dsimp; split_ifs with H
       · subst j; exact (h hj).elim
       simp
  right_inv:=fun ⟨j,hj⟩=>by
     dsimp; split_ifs with H; · subst j; rfl
     rfl

include hp
lemma keeps (x:I→E4){v:I→S.Tag}(hx:Q I x) (s:Finset I)(hv:∀ i∉ s, literal (v i)) :
    apply p x v = apply p (x ∘ ((↑): (↑s)→I)) (v ∘ fun i:s=>i.val) :=by
    have he(p' q:Finset I)(e:p'=q): apply p (x ∘ ((↑):↑p'→I)) (v ∘ Subtype.val) = apply p (x ∘ ((↑):↑q→I)) (v ∘ Subtype.val):= e ▸ rfl
    have h(q:Finset I)(hq:Disjoint q s): apply p (x ∘ ((↑): ↑(q∪s)→I)) (v ∘ Subtype.val)=apply p (x ∘ ((↑): (↑s)→I)) (v ∘ Subtype.val):=by
      induction q using Finset.induction_on with
      | empty => exact he _ _ (Finset.empty_union _)
      | @insert i t hi ih=>
        have his:i∉s:=Finset.disjoint_left.mp hq (mem_insert_self ..)
        specialize ih (hq.mono_left (subset_insert ..))
        refine ((he _ _ (Finset.insert_union i t s)).trans ?_).trans ih
        let e := adjoin (i:=i) (q:=t∪s) (notMem_union.mpr ⟨hi,his⟩)
        let Y:=x ∘ ((↑):↑(t∪s)→I); let w:=v ∘ ((↑):↑(t∪s)→I)
        let X:=x ∘ ((↑):↑(insert i (t∪s))→I); let u:=v ∘ ((↑):↑(insert i (t∪s))→I)
        have hX:Q _ X:=hp.shrink _ _ x Subtype.val hx Subtype.val_injective
        have hxe:X ∘ e = beside (sole (x i)) Y:=funext fun j=>by rcases j with ⟨_⟩ | _ <;> rfl
        have hve:u ∘ e= beside (sole (v i)) w:=funext fun j=>by rcases j with ⟨_⟩ | _ <;> rfl
        rw [show v i=(⟨(v i).fst,S.unit (v i).fst⟩:S.Tag) from Sigma.ext rfl (heq_of_eq (hv i his))] at hve
        change apply p X u=apply p Y w
        rw [hp.perm _ _ e X u hX,hxe,hve]
        exact hp.erase _ _ _ _ w (hxe ▸ hp.shrink _ _ X e hX e.injective)
    let e:↑(Finset.univ:Finset I)≃ I := (Equiv.subtypeUnivEquiv (fun i=> show i∈(Finset.univ:Finset I) from Finset.mem_univ i))
    calc apply p x v = apply p (x ∘ ((↑):↑(Finset.univ:Finset I)→I)) (v ∘ Subtype.val) := (hp.perm _ _ e x v hx).trans (by rfl)
         _ = _ := (he _ (Finset.univ \ s ∪ s) (Finset.sdiff_union_of_subset s.subset_univ).symm).trans (h _ sdiff_disjoint)
lemma restrict (x:I→E4)(hi:Q I x)(e:J→I)(he:Injective e)(v:I→S.Tag)(hc : ∀ i, (∀ j:J,e j≠i)→literal (v i)): apply p x v=apply p (x ∘ e) (v ∘ e):=by
    let s:Finset I:= Finset.univ.image e
    let f (j:J):s:=⟨e j,Finset.mem_image_of_mem _ (mem_univ ..)⟩
    have hf: Bijective f:=⟨fun j k hh=> he (congr_arg Subtype.val hh), fun ⟨i,hi⟩=>by
       obtain ⟨j,-,hj⟩:=Finset.mem_image.mp hi; exact ⟨j,Subtype.ext hj⟩⟩
    have hg:= keeps hp x hi s (fun i hh=>hc i fun j hj=>hh (Finset.mem_image.mpr ⟨j,mem_univ _,hj⟩))
    exact hg.trans <| (hp.perm _ _ (Equiv.ofBijective f hf) (x ∘ ((↑):↑s→I)) (v ∘ Subtype.val) (hp.shrink _ _ x Subtype.val hi Subtype.val_injective)).trans (by rfl)

end Undo
variable {I J:Type}[Fintype I][Fintype J]

def readingIdentity(o:E4)(m:ℕ): Undo.Identity S (S.Field m) (fun _ x=> orbitMargin R.port m x o) (fun I _ (x:I→E4) v=> R.fresh m x o (voices v)) := by
    constructor
    · intro I J x e hx he i hi k t ht; replace hx:=hx i hi k t ht
      let f:=Sum.map (g:=id (α:=Fin t.n)) e
      have hf:Injective f:=by rintro (i|i) (j|j) hv <;> simp only [f,Sum.map_inl,Sum.map_inr,id_eq, Sum.inl.injEq,reduceCtorEq,Sum.inr.injEq] at hv ⊢ <;> aesop -- check tactic
      convert (hx.comp hf) using 1; funext i; rcases i with i|i<;> rfl
    · intro I J hI hJ e x v hi; exact Reader.fresh_perm R m x o (voices v) e |>.symm
    intro I hI x a i v h
    let w:=stages (sole (S.unit i): Labels S fun _:Unit=>i) (voices v)
    have he:beside (sole (⟨i,S.unit i⟩:S.Tag)) v=(fun j=>⟨_,w j⟩):=funext fun j=>by cases j<;>rfl
    change R.fresh m _ o (voices _) = _; rw [he]; exact R.fresh_unit x o i (voices v) m a h

-- refine identified physical-unit deletion law also for non-selected true table

def momentIdentity (T:Table C.book)(hT:T.Hierarchy)(h:T.respects S): Undo.Identity S ℂ (fun _ x=>Injective x) (fun I _ (x:I→E4) v=>moment T x (voices v)) :=by
   constructor
   · exact fun _ _ _ _ hx he=>hx.comp he
   · intro I J _ _ e x v hv; exact (permuted hT hv e (a:=voices v)).symm
   intro I _ x o i v hi
   let z:=beside (sole o) x
   let t:=beside (sole (⟨i,S.unit i⟩:S.Tag)) v
   let n:=Fintype.card (Unit ⊕ I); let q:=runNames (Unit⊕I)
   let w:=beside (sole (C.book.one i)) (names (voices v))
   have hq: S.useAt T (points (z ∘ q)) (tags (voices t) ∘ q)=S.useAt T (points (z ∘ q)) (S.classTokens ∘ w ∘ q) :=by
       apply congr_arg; funext j
       change tags (voices t) (q j)= S.classTokens (w (q j))
       rcases q j with ⟨_⟩ | k
       · rfl
       · have hv:S.project _ (S.representative _ ((v k).snd)) = (v k).snd:= S.rep ..
         exact Sigma.ext rfl (heq_of_eq hv.symm)
   change moment T z (voices t) = _ -- coe notation?
   change S.useAt T (points (z ∘ q)) (tags (voices t) ∘ q)=_
   rw [hq,S.at_project T hT.laws.toSymmetric h (by exact runs_conf.mpr hi) (w ∘ q),← T.readAt]
   exact (local_one_mem T i _ x hT.laws hi).trans ((observed (T:=T) (voices v) x).symm)
end YM.OPE.Sparse
