import YM.OPE.Compatible.Glades.Process
/-!
# Add witnesses along a run, keep the originals

Embed the principal copy orbit into another. E' in the other can be
under different alignments; require only that the old part retains its
alignment. Only need this *stepwise* on the supported interval of this
extra copy. Preserve the actual sources on the old part (not a
reselected one).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Wilson MeasureTheory
open Push Marker Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Stem
open scoped Topology Classical
variable {V I J W : Type}[Fintype V][DecidableEq V]{G:Gauge}{n n':Side}{H:History G}{N p m:ℕ}
variable (P:Ensemble V)(P':Ensemble W)(M:V ↪ W)
/-- Principal part. -/
structure Screenlet : Prop where
   start : M P.v=P'.v
   acts : P'.move ∘ M=P.move
   runs i : (P'.perms (M i)) ∘ M=M ∘ (P.perms i)
namespace Stem
def cropStem (X:Stem W G n) : Stem V G n := ⟨X.home ∘ M,X.oil ∘ M,X.gas ∘ M⟩
variable {P P'}
omit [Fintype V][DecidableEq V] in
lemma Marked.high {R : Rep G n} {E' : W→Site n}{X:Stem W G n}
   (h : Marked R E' P' X) (hM:Screenlet P P' M): Marked R (E' ∘ M) P (cropStem M X):=by
   refine ⟨fun i hi=>?_,fun i hi=>?_,fun i=>h.spends _⟩
   · change X.home (M i)=affine _ _ (X.home (M P.v)); rw [hM.start, ← (@congr_fun _ _ _ _ hM.acts i)]; exact h.sym _ (fun H=>hi (M.injective (H.trans hM.start.symm)))
   change X.oil (M i) = _ ∧ profile _ (X.gas (M i))= _; unfold cropStem; dsimp only; simp_rw [Function.comp_apply,hM.start]; -- second comp only inside? check
   rw [← congr_fun hM.acts i]; exact h.shine _ (fun H=>hi (M.injective (H.trans hM.start.symm)))
variable {x:V→ Site n}{E:V→ Site n}{X:Stem V G n}
variable {E': W→Site (H.S.side m p)}
variable [Fintype W]
omit [Fintype V][DecidableEq V] in
lemma discovered {X:Stem V G (H.S.side m p)}(hM:Screenlet P P' M)(x:W→Site (H.S.side m p))(h : H.Selected)(hn:m≤N)
    (hx:X.home = x ∘ M) (hv:∀ i,i≠P'.v→ x i=affine (P'.move i).1 (E' i) (x P'.v)) (ht: Marked (H.rep N p m) (E' ∘ M) P X) :
    ∃ X':Stem W G (H.S.side m p), cropStem M X'=X∧ X'.home=x ∧ Marked (H.rep N p m) E' P' X':=by
    obtain ⟨Y,hY,hKY,hAY,hV⟩:= submit h hn (X.oil P.v) (ht.spends P.v) x hv
    have h0(k:V):Y.oil (M k)=X.oil k ∧ profile (H.rep N p m).activities (Y.gas (M k))=profile (H.rep N p m).activities (X.gas k):=by
        by_cases he:k=P.v
        · subst k; rw [hM.start,hKY,hAY]; exact ⟨rfl,rfl⟩
        have ht': M k ≠ P'.v:=by rw [← hM.start]; exact M.injective.ne he
        rw [(hY.shine _ ht').1,(hY.shine _ ht').2,(ht.shine k he).1,(ht.shine k he).2,hKY,hAY,show P'.move (M k)=P.move k from congr_fun hM.acts k]; exact ⟨rfl,rfl⟩
    let f(i:W):= if h:i∈Set.range M then X.gas h.choose else Y.gas i
    have hi (k:V):f (M k)=X.gas k:=by unfold f; rw [dif_pos (Set.mem_range_self k)]; exact congr_arg _ (M.injective ((Set.mem_range_self (f:=M) k).choose_spec))
    let Z:= Stem.mk x Y.oil f
    have hz: cropStem M Z=X := by
        have he:Y.oil ∘M=X.oil:= funext fun i=>(h0 i).1; change Stem.mk _ _ _=X; rw [show x ∘ M=X.home from hx.symm,he,(show f ∘M=X.gas from funext hi)]
    have hf : ∀ i, Dominated (f i):=by intro i; unfold f; split <;> first| exact ht.spends _| exact hY.spends _
    refine ⟨Z,hz,rfl,(counterpart h hn hY Z hV rfl (fun i=>?_) hf).1⟩
    by_cases hh:i∈ Set.range M; · obtain ⟨j,rfl⟩:= hh; change _=profile _ (f _); rw [hi]; exact (h0 _).2
    change _=profile _ (f i); unfold f; rw [dif_neg hh]
end Stem
end YM.MergeProof.Ribbons.ManyCopies
