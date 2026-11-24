import YM.MS.Train.Lark
/-!
# Ambiance proof spaces. Laurent uniform equality first.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Train
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl
open Signal Book Convolve
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z:Flats G}{f g:Coat G}{b:Bool}{t q:ℤ}
abbrev Spotty (f g:Coat G): Prop:= f=ᶠ[dotty] g
-- fillings of property valid under restricting ℓ supp
lemma facade (F:Flats G)(P:I→ℕ→ Mob G→ Prop)(H:I→ℂ)(V:Filter I)(h:∀ z k,P z k 0)(he:∀ i,∀ᶠ z in V,P z i (F i (H z))) : ∀ᶠ z in V,∀ i,P z i (F i (H z)):= by
   filter_upwards [(eventually_all_finset F.support).mpr (fun i _=> he i)] with x hx i; by_cases hi:i∈ F.support; · exact hx i hi
   rw [Finsupp.notMem_support_iff.mp hi]; exact h x i
lemma two (F X:Flats G)(P:I→ℕ→ Mob G→Mob G→ Prop)(H:I→ℂ)(V:Filter I)(h:∀ z k,P z k 0 0)(he:∀ i,∀ᶠ z in V,P z i (F i (H z)) (X i (H z))) : ∀ᶠ z in V,∀ i,P z i (F i (H z)) (X i (H z)):= by
   filter_upwards [(eventually_all_finset (F.support∪X.support)).mpr (fun i _=> he i)] with x hx i; by_cases hf:i∈F.support; · exact hx _ (Finset.mem_union_left _ hf)
   by_cases hH:i∈ X.support; · exact hx _ (Finset.mem_union_right _ hH)
   rw [Finsupp.notMem_support_iff.mp hf, Finsupp.notMem_support_iff.mp hH]; exact h x i
abbrev Pact (F X:Flats G): Prop:=∀ i, Spotty (F i) (X i)
lemma took (h:Pact F X): ∀ᶠ i in dotty,∀ k,F k i=X k i:= two F X (fun _ _ x y=>x=y) id dotty (fun _ _=>rfl) h
lemma treaty (p:ℂ)(hp:∀ i:ℕ,F i p=X i p)(h:ℕ)(y s:ℝ): Parade F h y s p=Parade X h y s p:= by
    rw [ Page (F.support ∪ X.support) Finset.subset_union_left, Page (F.support ∪ X.support) Finset.subset_union_right, Finset.sum_apply,Finset.sum_apply]; simp_rw [hp]
lemma prom (h:Pact F X)(n:ℕ)(s y:ℝ): Spotty (Parade F n y s) (Parade X n y s):= (took h).mono fun i hi=> treaty i hi n y s
lemma same_jump (h:Pact F X)(Q:ℂ→ MH (Mob G))(n:ℕ): Pact (blast n (tapeL Q) F) (blast n (tapeL Q) X):= by
   intro k; by_cases hm:k<n; rw [bland hm,bland hm]; obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le' (le_of_not_gt hm); rw [blade,blade]; exact (h j).mono fun i hi=> congr_arg (Q i) hi
lemma pact0 (h:∃ k:ℤ,k<0∧∀ i, To (F i) (grade k G)): Pact F 0:= by
    obtain ⟨k,hk,h⟩:=h; apply (fun i=> (h i).mono (fun j hj=>?_)); ext m l; replace hj:Issue k (F i j):= hj; exact hj m l (by omega)
-- repeat Prop combinator
abbrev SeedP (P:Coat G→Prop)(F:Flats G): Prop:=∀ i, P (F i)
structure Heap (P:Coat G→ Prop): Prop where
    zero: P 0
    add (f g:Coat G): P f→ P g→ P (f+g)
lemma Heap.single {P:Coat G→Prop}(hp:Heap P)(h:P f)(n:ℕ): SeedP P (Finsupp.single n f):= by intro i; simp only [Finsupp.single_apply]; split; exact h; exact hp.zero
lemma Heap.plus {P:Coat G→Prop}(hp:Heap P)(h:SeedP P F)(ht:SeedP P X): SeedP P (F+X):= fun i=> hp.add _ _ (h i) (ht i)
lemma Heap.sum {P:Coat G→Prop}(hp:Heap P){F:I→ Flats G}(s:Finset I)(h:∀ i∈s, SeedP P (F i)): SeedP P (∑ i∈s, F i):= by
    classical
    induction s using Finset.induction with
    | empty=> rw [Finset.sum_empty]; exact fun i=> hp.zero
    | insert b t hb ih=> rw [Finset.sum_insert hb]; exact hp.plus (h b (by simp)) (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))
lemma Heap.pipe {P:Coat G→Prop}(hp:Heap P)(M:MH (Coat G))(F:Flats G)(s:ℕ)(h:∀ i,P (M (F i))): SeedP P (blast s M F):= by rw [blap,Finsupp.sum]; exact hp.sum _ (fun i _=> hp.single (h i) _)
lemma Heap.explo {P:Coat G→Prop}(hp:Heap P)(M:Signal.Pair (Coat G))(X F:Flats G)(h:∀ i j,P (M (X i) (F j))): SeedP P (explode M X F):= by rw [explodeL,Finsupp.sum]; exact hp.sum _ (fun i hi=> hp.sum _ (fun j _=> hp.single (h i j) _))
lemma Weighted : Heap (mer (G:=G)):= ⟨mer.zero,fun _ _=>mer.add⟩
lemma washed (P:LeanC G) : Heap (fun φ=>To φ P):= ⟨Eventually.of_forall (fun _=> P.zero_mem),fun _ _ h ht=> ( h.and ht).mono fun _ hp=> P.add_mem hp.1 hp.2⟩
lemma real_axis (P:LeanR G): Heap (fun φ=>realAlong φ P):= ⟨Eventually.of_forall (fun _=> P.zero_mem),fun _ _ h ht=> Eventually.mono (Eventually.and h ht) (fun _ hi=> P.add_mem hi.1 hi.2)⟩
-- typical
abbrev Cap (n:ℤ)(F: Flats G): Prop:=∀ i,To (F i) ( grade n G)
lemma Cap.rise (h: Cap t F)(he:t≤q): Cap q F:= fun i=> (h i).mono fun j hj=> show Issue q (F i j) from fun n l h=> (show Issue t (F i j) from hj) n l (by omega)
lemma re_part (x:ℂ)(h:star x=x)(Q:LeanR G){f:Mob G}(hv:f∈Q): x•f∈Q:= by obtain ⟨y,hy⟩:= Complex.conj_eq_iff_real.mp h; rw [hy,reality]; exact Q.smul_mem _ hv
end YM.MS.Train
