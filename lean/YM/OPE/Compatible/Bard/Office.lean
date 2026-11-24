import YM.OPE.Compatible.Bard.Span
/-! Launch the requested site patterns without internal collisions excluding needed slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Arcade
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave
open scoped Topology BigOperators Classical
variable {X V B T: Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U F K:Finset X}{m j:X→ℕ}
    [Fintype V][DecidableEq V][Fintype T][DecidableEq T][Fintype B]
    {G:Gauge}{C:Family G}{p N b d k:ℕ}{l:ℕ→ℕ}{A:Allot C} {z e:ℝ}
variable {P:Ensemble V}{P':Ensemble T}{E:Track C.path V p}{o:X→Track C.path V p}
    {E':Track C.path T p}{o':X→Track C.path T p} {f:V ↪ T}{a:T→B}
variable (h:Arcade C P' f a D U m j N p P E o b l E' o' k)
    (X': Extra.Histories.Music (C.labels.level d) C.path N p) (hΨ : Solvent (A:=A) X')
set_option quotPrecheck false
local notation "L'"=> (C.labels.level d).Index
local notation "W"=> brim D U
set_option quotPrecheck false
variable (v:X)(hv:v∈U)
include h hΨ v hv
lemma pay_local (H:C.Makes)(hb:1 ≤ b)(hp:C.ref d < k)(hn:k ≤ N)(hk:m ⊥ ≤ k)(ht:Fintype.card B*(places X+Fintype.card (C.labels.level d).Index) ≤ A.r N)
    (p₀:brim D U→ℕ)(p':∀ i,C.label (p₀ i))(u:brim D U→ℝ) (w:X→ℕ) -- del
    (he:Migrating C.path k p N (o v))(hy:∀ i:brim D U,C.ref (p₀ i) ≤ w i.val ∧ w i.val<N ∧ finishAt D m i.val ≤ w i.val+1 ∧ Migrating C.path (w i.val+1) p N (o i.val)∧ 0 < u i∧2*u i* Spindle.paid C (p₀ i) (w i.val+1) N p (p' i)≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels (p₀ i) (w i.val+1)) :
    let z: T ×(brim D U⊕ (C.labels.level d).Index)→ Config G (C.side N p)→ℂ :=fun i=> i.2.elim (fun j=>stepUp (P'.move i.1) (o' j.val N i.1) (C.O N p (p' j) 0)) (fun j=>stepUp (P'.move i.1) (o' v N i.1) (C.O N p (lyric C X' k j) 0))
    ∃ M:Lights A P N p (brimEnd D (C.labels.level d).Index U (finishAt D m) k) N b E (o∘columns D (C.labels.level d).Index U v), ∃ Y, Session P' f M (birth (ManyCopies.Names T _) (C.path.rep N p N) z) Y (shades' D U v a _) E' (o'∘ columns D (C.labels.level d).Index U v) ∧
       (∀ i:brim D U,M.bottom (.inl i)= Run.Below C.path (u i) (w i.val+1) (finishAt D m i.val)) ∧ (∀ j:(C.labels.level d).Index,M.bottom (.inr j)= ballot C k d ∧ Stamp (N:=N) P (C.localSection d) (E k) ((X'.tone k).plays (sonnet C X' k j)) ((M (.inr j)).X k)):=by
    intro z; have hθ : C.ref 0 ≤ m ⊥:= h.bed.head.le
    have hv'(i:brim D U): i.val∈allUp D U:=mem_union_right _ i.2; have hf:v∈allUp D U:=mem_union_left _ hv
    have h0 x'(t:ℕ)(hq:k ≤ t)(ht:t ≤ N)(hi:x'≠P.v) : o v t x'=affine (P.move x').1 (E t x') (o v t P.v):=by
       rw [← h.honors _ _ hf hq ht,comp_apply,h.pays _ _ hf hq ht (f x') (by rw [← h.fly.start]; exact f.injective.ne hi),← h.fly.start,show P'.move (f x')= _ from congr_fun h.fly.acts x'] -- last rewrite pattern
       rw [show E' t (f x')= _ from congr_fun (h.turns t hq ht) x']; rfl
    have hE(q): q∈allUp D U → ∀ (d:ℕ)(w:C.label d)(x:V),stepUp (P'.move (f x)) (o' q N (f x)) (C.O N p w 0)= stepUp (P.move x) (o q N x) (C.O N p w 0):=by
        intro hi d t x; rw [show o' q N (f x)=o q N x from congr_fun (h.honors _ _ hi hn le_rfl) x, show P'.move _ = P.move _ from congr_fun h.fly.acts x]
    have hK(i:brim D U): ∃ x: Line A P N p (finishAt D m i.val) N b E (o i.val), x.w (finishAt D m i.val)=Run.Below C.path (u i) (w i.val+1) (finishAt D m i.val)∧ Budges P C.path N p (far C.path.levels N) (x.w N) (E N) (x.X N) (fun t=> z (f t,.inl i)):=by
       obtain ⟨hb',hP,hε,hJ,hv,hX⟩:=hy i; let j:=finishAt D m i.val; have hc:m ⊥≤ j:= lower_earliest D U m h.bed.plan _ (hv' i)
       have hf: w i.val+1 ≤roof U m N i.val:= (show w i.val+1≤N from hP).trans (show N ≤ roof U m N i.val from (if_neg ((on_brim ..).mp i.2|>.1)).ge)
       have hg: N=roof U m N i.val:=(if_neg ((on_brim ..).mp i.2|>.1)).symm
       obtain ⟨L,hL,hM,-⟩:= fresh_line A P (p' i) H hb (hθ.trans hc) hb' hε hP ⟨fun i hi he=>h.bed.moves.mare i (hc.trans hi) he⟩ hJ (fun t hk' hj=> h.bed.pare _ (hv' i) t hk' (hj.trans_le hf)) (fun t hp hg' x' hi=> h.bed.echo _ (hv' i) t (hε.trans hp) (hg'.trans_eq hg) x' hi) hv hX
       exact ⟨L,hL,(show _ from (funext (fun x=> (hE i.val (hv' i) _ (p' i) x).symm):_=(fun t=> z (f t,.inl i))) ▸ hM)⟩ -- motive
    have hJ(i:L') : ∃ x:Line A P N p k N b E (o v), x.w k= ballot C k d ∧ Budges P C.path N p (far C.path.levels N) (x.w N) (E N) (x.X N) (fun t=>z (f t,Sum.inr i)) ∧ Stamp (N:=N) P (C.localSection d) (E k) ((X'.tone k).plays (sonnet C X' k i)) (x.X k):=by
        obtain ⟨x,hx,hB,hx'⟩:= pointer X' hΨ H hp hn (hθ.trans hk) ⟨fun i hi ht=> h.bed.moves.mare i (hk.trans hi) ht⟩ he hb (fun i hk ht v hv=> h0 v i hk ht hv) i
        exact ⟨x,hx,(funext (fun a=> (hE v hf _ (lyric C X' k i) a).symm): _=(fun t=> z (f t,.inr i))) ▸ hB,hx'⟩
    choose L hL hM using hK; choose L'0 hT hB hU using hJ
    let u₀ : Lights A P N p (brimEnd D (C.labels.level d).Index U (finishAt D m) k) N b E (o∘ columns D (C.labels.level d).Index U v):= Sum.rec L L'0 -- motif
    have hp (i:X)(hi:i∈allUp D U)(g:Config G (C.side N p)→ℂ)(u:T)(hx:u≠P'.v) : stepUp (P'.move u) (o' i N u) g= stepUp (P'.move u) (E' N u) (stepUp (P'.move P'.v) (o' i N P'.v) g) :=by rw [P'.spring,flyF]; exact congr_arg (fun x=> stepUp (P'.move u) x g) (h.pays _ _ hi hn le_rfl u hx)
    have hu(i:T×(brim D U⊕(C.labels.level d).Index)): Continuous (z i):=by
       have he(d:ℕ)(v:C.label d)(o)(x:Motion): Continuous (stepUp x o (C.O N p v 0)):=by
           unfold stepUp scalar; split <;> first| exact Continuous.star ((C.continuousO ..).comp (continuous_pull ..))|exact Continuous.comp (C.continuousO ..) (continuous_pull ..) -- inspect
       rcases i with ⟨v,x|x⟩; exact he ..; exact he ..
    obtain ⟨X',hX⟩:= Session.begin_p (L:=u₀) H ((lives D (C.labels.level d).Index h v hf (Finset.Subset.refl _)).sub hn le_rfl) (shades' D U v a (C.labels.level d).Index) z (fun i=>by cases i; exact hM _; exact hB _) hu (fun j a hi=>by
       cases j; next j=> exact hp j.val (hv' j) _ a hi
       next=> exact hp v hf _ a hi) (begun D (C.labels.level d).Index h (Finset.Subset.refl _) hf hn le_rfl ht)
    exact ⟨_,_,hX,hL,fun i=> ⟨hT i,hU i⟩⟩
end YM.OPE.Arboreal.Arcade
