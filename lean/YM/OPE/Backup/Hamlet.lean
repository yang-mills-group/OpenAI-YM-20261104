import YM.OPE.Replicas.Menu
import YM.MergeProof.South.Hearth
/-!
# Backup name budget

Keep forbidden monomials out of the radius estimates even with secondary name
insertions (needed e.g. a collocated basis to refer back to MATCH choices
after a propagation). Technique: use the all-names Census but with exact shadow
for the RG witnesses of these contents. Artificial play for any one step only,
with the forbidden monomials cut back off before growth of radii. This works
because Occupancy (not spacing) suffices for the actual step on such a play.
Only agrees with a true constructed cutoff polynomial on the admissible names,
downward closed. Never read the cost on extraneous parts after repaying.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Backup
open Function Set Finset Filter Lattice RG Wilson Pressure MergeProof Accent Ribbons Menu Source
open Extra.Histories Push Marker Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {V ι : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{δ:ℝ}
-- Use (not necessarily symmetric) mask on actual Poly on every level
structure Ward (B:Census V) where
   ready : B.Mode→ Prop
   blank : ready B.quiet
   down {i j}: i.val ⊆ j.val → ready j → ready i
   fire j : ready (B.fire j)
protected def Ward.all (B:Census V) : Ward B:= ⟨fun _=>True,trivial,fun {_ _} _ h=>h,fun _=>trivial⟩
variable (L: Ward B)
namespace Ward
def Writes (p q:Poly B) := ∀ i, L.ready i → p.part i=q.part i
lemma Writes.have_ {p q:Poly B} (h:L.Writes p q) {i:B.Mode} (hs:L.ready i) : p.part i=q.part i:= h i hs
lemma Writes.fireEq {p q:Poly B}(h:L.Writes p q) (j:V) : p.part (B.fire j)=q.part (B.fire j):= h _ (L.fire j)
variable {L} {p q a b:Poly B}(hp:L.Writes p q)(ha:L.Writes a b)
lemma reflex (L:Ward B)(p:Poly B) : L.Writes p p:= fun _ _=>rfl
lemma Writes.symmx (h:L.Writes p q): L.Writes q p:= fun i hi=>(h i hi).symm
lemma Writes.seq (hp:L.Writes p q)(hq:L.Writes q b): L.Writes p b:= fun i hi=>(hp i hi).trans (hq i hi) -- implicit
lemma Writes.plus (hp:L.Writes p q)(ha:L.Writes a b) : L.Writes (p+a) (q+b):=by intro i hi; simp only [Poly.part_plus,hp i hi,ha i hi];
lemma Writes.paint (hp:L.Writes p q)(z:ℂ) : L.Writes (z • p) (z • q):=fun i hi=> congr_arg (z * ·) (hp i hi)
lemma Writes.product (hp:L.Writes p q)(ha:L.Writes a b): L.Writes (p*a) (q*b):=by
   intro i hi; rw [Poly.part_mul,Poly.part_mul]; refine sum_congr rfl fun j _=>sum_congr rfl fun k _=>?_; split_ifs with h; · rw [hp j (L.down (by rw [← h.2]; exact subset_union_left) hi), ha k (L.down (by rw [← h.2]; exact subset_union_right) hi)];
   rfl
lemma many (s:Finset ι){F G:ι→ Poly B}(h:∀ i∈s,L.Writes (F i) (G i)) : L.Writes (∑ i∈s,F i) (∑ i∈s,G i):=by intro i hi; simp_rw [Poly.part_sum]; exact sum_congr rfl fun k hk=>h k hk i hi
lemma productMany (s:Finset ι){F G:ι→ Poly B}(h:∀ i∈s,L.Writes (F i) (G i)) : L.Writes (∏ i∈s,F i) (∏ i∈s,G i):=by induction s using Finset.induction_on with
    | empty=> rw [Finset.prod_empty,Finset.prod_empty]; exact reflex L _
    | @insert i s hi IH=> rw [prod_insert hi,prod_insert hi]; exact (h _ (mem_insert_self ..)).product (IH fun i hi=>h _ (mem_insert_of_mem hi))
lemma Writes.powers (hp:L.Writes p q)(i:ℕ):L.Writes (p^i) (q^i):= by induction i with
   | zero=>rw [pow_zero,pow_zero]; exact reflex L _ -- defeq?
   | succ i ih=>rw [pow_succ,pow_succ]; exact ih.product hp
lemma Writes.passes [Fintype V] (hp:L.Writes p q): L.Writes (Poly.pass p) (Poly.pass q):= many _ (fun i _=> (hp.powers i).paint _)
-- clearing
variable (L)
def clear (p:Poly B) : Poly B := Poly.inject (fun i=> if L.ready i then p.part i else 0)
lemma clears (p): L.Writes (L.clear p) p:=fun i hi=> if_pos hi
lemma zero_off (p) {i} (hi:¬ L.ready i) : (L.clear p).part i=0:= if_neg hi
section
variable {o:V→Site f}{u:Config G f→Poly B}{P:Support f}
    {F:Support f→ Config G f→Poly B}{K:Box f→ Config G f→Poly B}{M:ℕ}{w w':V→ℝ}{x e d t:ℝ}
lemma nonemptyAt (U:Config G f)(h:L.clear (u U) ≠ 0): u U ≠ 0:=by
   intro he; apply h; rw [he]; ext i; by_cases hx:L.ready i; · exact L.clears _ _ hx
   exact L.zero_off _ hx
lemma hidden (h:Borne o P u δ) : Borne o P (fun U=> L.clear (u U)) δ:=by
   refine ⟨fun U V hs ht=> congr_arg _ (h.home U V hs ht), fun σ U=> congr_arg _ (h.turns σ U),fun i=>?_,fun U i hi=> ?_⟩
   · change Measurable fun U=> if L.ready i then (u U).part i else 0; split; exact h.me i; exact measurable_const
   by_cases hx:L.ready i
   · erw [L.clears (u U) i hx]; exact h.scope _ _ hi
   exact L.zero_off _ hx
lemma kerning (h: Burns o P u δ) : Burns o P (fun U=>L.clear (u U)) δ:= ⟨hidden _ h.toBorne,fun U he=> h.permits U (nonemptyAt _ U he),fun U=> (L.clears (u U) B.quiet L.blank).trans (h.sil U)⟩
lemma river {p:Box f} (h:Flow o p u δ) : Flow o p (fun U=>L.clear (u U)) δ:= ⟨hidden _ h.toBorne,fun U he=> h.permits U (nonemptyAt _ U he)⟩
lemma retaining {p:Poly B}(h:rises p): rises (L.clear p):=by
    intro i hi; have hx: L.ready i:= not_not.mp (mt (L.zero_off p) hi); exact h _ (fun he=>hi ((L.clears p _ hx).trans he))
lemma carton (h:Carton o F K t) : Carton o (fun i U=>L.clear (F i U)) (fun i U=> L.clear (K i U)) t := ⟨fun i=> ⟨kerning _ (h.exp i).1, fun U=> L.retaining (h.exp i|>.2 U)⟩,fun i=> ⟨river _ (h.flag i).1,fun U=> L.retaining (h.flag i|>.2 U)⟩⟩
variable {L}
lemma field_parts {u u':Box f→Poly B}(h:∀ i,L.Writes (u i) (u' i))(P:Support f) : L.Writes (field u P) (field u' P):=many _ fun p _=> by
    unfold grid; split_ifs; exact productMany _ fun i _=>h i; exact reflex L _
variable (L)
lemma restore_clear [Fintype V] (R:Rep G f)(u:V→ Config G f→ℂ)(p:V→Box f→ Config G f→ℂ) (F:Support f→ Config G f→Poly B)(K:Box f→ Config G f→Poly B)(U:Config G f):
    L.Writes (restore R u p F K U) (restore R u p (fun i U=>L.clear (F i U)) (fun i U=>L.clear (K i U)) U):= ((Writes.product ((Writes.plus (reflex L _) (many _ (fun i _=> Writes.symmx (L.clears (F i U))))).passes) (field_parts (fun p=> Writes.plus (reflex L _) (Writes.symmx (L.clears (K p U)))) _))).paint _ -- paren edit
/-- Moderate or ordinary separation reserve on *permitted* monomials -/
def Cares (L:Ward B) (o:V→Site f)(M:ℕ)(w w':V→ℝ)(e:ℝ) := ∀ i:B.Mode, L.ready i→2 ≤ i.val.card → ∀ p:Support f,i.val.image o ⊆ p → Poly.toll w' i ≤ Poly.toll w i * Real.exp (e*coverNumber M p)
lemma towed_clear {F:ι→ Config G f→Poly B}{r:ι→Support f}(h:Towed w r F M (d+e) x)(H:∀ i,Borne o (r i) (F i) t)(ht:∀ i U,rises (F i U))(hp:Cares L o M w w' e)(hx:∀ i,0<w i)(hX:∀ i,0<w' i): Towed w' r (fun i U=> L.clear (F i U)) M d x:=by
   obtain ⟨a,ha,h,hB⟩:=h
   let g i:= Real.exp (e*coverNumber M (r i))*a i
   have hh(i):0 ≤ a i:= (hB i|>.fares hx).1
   have hf: Summable g:= by
      obtain ⟨m,hi,hM⟩:= Finset.exists_max_image (univ:Finset (Support f)) (fun X=> Real.exp (e*coverNumber M X)) Finset.univ_nonempty
      refine (ha.mul_left (Real.exp (e*coverNumber M m))).of_nonneg_of_le (fun i=> mul_nonneg (Real.exp_pos _).le (hh _)) (fun i=> mul_le_mul_of_nonneg_right (hM (r i) (Finset.mem_univ _)) (hh _))
   refine ⟨g,hf,fun x=>?_,fun i=> ?_⟩
   · convert! h x using 1; ext i; unfold g; split_ifs <;> simp only [add_mul,Real.exp_add] <;> ring
   obtain ⟨u,h,hp',hv⟩:= hB i
   let α (j:B.Mode):= L.ready j ∧ 2 ≤ j.val.card ∧ j.val.image o ⊆ r i
   let b (j:B.Mode):= if α j then u j else 0
   have hb(i):0 ≤ b i:=by unfold b;split;exact h _; rfl
   refine ⟨b,hb,fun U j=> ?_,?_⟩
   · unfold b; split
     next he=> exact (le_of_eq (congr_arg _ (L.clears (F i U) j he.1))).trans (hp' U j)
     next he=>
      change ¬ α j at he
      rw [show (L.clear (F i U)).part j=0 from Classical.byContradiction (fun h=>?_),norm_zero]
      have h1:= not_not.mp (mt (L.zero_off (F i U)) h); rw [L.clears (F i U) j h1] at h; exact he ⟨h1,ht i U j h,(H i).place _ _ h⟩
   let P:= Real.exp (e*coverNumber M (r i)); have ht':0 ≤ P:= (Real.exp_pos _).le
   refine le_trans ?_ (mul_le_mul_of_nonneg_left hv ht'); unfold wordsPrice; rw [Finset.mul_sum]; refine sum_le_sum fun j _=>?_ ; unfold b
   split
   next hh=> rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ((hp j hh.1 hh.2.1 (r i) hh.2.2).trans_eq (by ring)) (h j)
   rw [mul_zero]; exact mul_nonneg ht' (mul_nonneg (Poly.worth hx j).le (h j))
end
end Ward
end YM.OPE.Backup
