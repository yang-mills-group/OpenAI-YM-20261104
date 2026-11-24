import YM.OPE.Compatible.Bower.Ballast
/-!
# Handoff terminal clock at vertex replacing its usual route promise.
The promised capacity already paid. Reserve an outgoing port then
can call from palette without perturbing anyone else.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology BigOperators Classical
variable {X V I J W K: Type}[Fintype V][DecidableEq V][Fintype W][DecidableEq W][Fintype K][DecidableEq K][Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    {G:Gauge}{C:Family G}{p n N b d k l:ℕ}{A:Allot C}
variable {P: Ensemble V}{P':Ensemble K}{E : Track C.path V p}
open Lights
variable {O: I→ Track C.path V p}{s:I→ℕ} {t j:J→ℕ}{O': J→Track C.path V p}{F:Fibers (I⊕W) J}
omit [Fintype V][DecidableEq V][DecidableEq W][DecidableEq I][Fintype J] in
lemma Binding.focused (h:Bind C P E F O O' n s t j) (x:J)(hp:¬ F.SingleFiber x) : Bind C P E F O O' n s (update t x n) (update j x n):=by
   have he:t x ≤ n := (h.ahead x hp).1.trans (h.ahead x hp).2; refine ⟨h.fell,?_,?_,?_,?_,?_,?_,?_,h.embers⟩
   · intro y hy; rw [update_of_ne (by rintro rfl; contradiction:y≠x)]; exact h.elder y hy
   · intro y hy; by_cases hf:y=x
     · subst y; rw [update_self]; exact lt_of_lt_of_le (h.keep x hp) he
     rw [update_of_ne hf]; exact h.keep y hy
   · intro y hy; by_cases hf:y=x
     · subst y; rw [update_self,update_self]; exact ⟨le_rfl,le_rfl⟩
     rw [update_of_ne hf,update_of_ne hf]; exact h.ahead y hy
   · intro y hy; by_cases he:y=x
     · subst y; rw [update_self]; exact ⟨fun t ht he=>False.elim (by omega)⟩
     rw [update_of_ne he]; exact h.pins y hy
   · intro y hy i hi hk; by_cases he:y=x
     · subst y; rw [update_self] at hi; exact False.elim (by omega)
     rw [update_of_ne he] at hi; exact h.parents y hy _ hi hk
   · intro y hy; by_cases he:y=x
     · subst y; rw [update_self]; exact ⟨fun t ht he=>False.elim (by omega)⟩
     rw [update_of_ne he]; exact h.periods y hy
   intro y n hn hh; by_cases hf:y=x
   · subst y; rw [update_self] at hn; exact h.authorized x n (he.trans hn) hh
   rw [update_of_ne hf] at hn; exact h.authorized y n hn hh
set_option quotPrecheck false
section
variable {M: Lights A P N p s (n+1) b E O}
-- assign replacements along all other Lines with explicit clock transport.
namespace Lights
omit [Fintype V][DecidableEq V] in
private lemma depot {o:Track C.path V p}{a a':ℕ}(h:a=a')(L:Line A P N p a (n+1) b E o):∃ S:Line A P N p a' (n+1) b E o,S.w=L.w ∧ S.X=L.X:=by subst a'; exact ⟨L,rfl,rfl⟩
lemma dock_inlet {E':Track C.path K p}{O':I→ Track C.path K p}{ι:V ↪ K}{χ:Guard (Names K I)}
    {U:I→ Stem K G (C.S.side (n+1) p)}{R:Config G (C.S.side (n+1) p)→ Marker.Poly (Names K I)}
    (h: Session P' ι M R U χ E' O') (x:I)(q:I→ℕ) (hq:∀ i,i≠x→q i=s i)
    (L:Line A P N p (q x) (n+1) b E (O x))(hp:L.X (n+1)=M.tips x)(hz:L.w (n+1) ≤ M.asks x):
    ∃ M':Lights A P N p q (n+1) b E O, Session P' ι M' R U χ E' O' ∧ M' x=L ∧ ∀ i,i≠x→ (M' i).X=(M i).X ∧ (M' i).w=(M i).w:=by
    have hP(i):∃ S:Line A P N p (q i) (n+1) b E (O i),(i≠x→ S.w=(M i).w ∧ S.X=(M i).X) ∧ (i=x → HEq S L):=by
      rcases eq_or_ne i x with rfl|he
      · exact ⟨L,fun h=> False.elim (h rfl),fun _=> HEq.rfl⟩
      obtain ⟨S,hs,h⟩:= depot (hq i he).symm (M i); exact ⟨S,fun _=>⟨hs,h⟩,fun hh=>False.elim (he hh)⟩
    choose S hs using hP; change Lights A P N p q (n+1) b E O at S -- issue
    have he: S x=L:= eq_of_heq ((hs x).2 rfl);
    have hh: S.tips=M.tips:=by
       funext i; by_cases h:i=x
       · subst i; unfold Lights.tips; rw [he]; exact hp
       unfold Lights.tips; rw [((hs i).1 h).2]
    have hφ: S.asks≤ M.asks:=by
       intro i; by_cases h:i=x
       · subst i; unfold Lights.asks; rw [he]; exact hz
       unfold Lights.asks; rw [((hs i).1 h).1]
    exact ⟨S,⟨h.live,fun i=> (h.seen _).trans (congr_fun hh i|>.symm), h.stood,Owned.inhibit _ h.ship (S.asks_pos) hφ⟩,he,fun i h=> ((hs i).1 h).symm⟩ -- symm not And.symm?
end Lights
end
end YM.OPE.Allot
