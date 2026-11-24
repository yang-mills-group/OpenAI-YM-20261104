import YM.FVAAlt2.Winder.Money
import YM.RegulatorIR.Budget.Draft
/-! # Anchored variation. First-order proof, not norms on aggregated field-ray polynomials! -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget.FVAAlt2.Wind
open Function Tuple Layer Packet Set Filter
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y Z W : Type} {l:Filter W} {K: Layer X X} {U: W→Layer X X} {C D : ℝ≥0∞} {r s:ℕ}

structure Pivot (l:Filter W)(C:ℝ≥0∞) (v:Packet X r) (F:W→ Packet X r) : Prop where
   high : C≠⊤
   earns : ∀ x:X,∀ i:Fin r,Earn l C (fun k:Hold i x=> v k.val) (fun w k=> F w k.val)
structure SplitT (l:Filter W)(C:ℝ≥0∞)(K:Layer X Y)(U:W→Layer X Y): Prop where
   high : C≠⊤
   earns : ∀ x:X,Earn l C (K x) (fun w=>U w x)
   up : ∀ y:Y,Earn l C (swap K y) (fun w=>swap (U w) y)
variable {v u:Packet X r}{F G: W→Packet X r}
lemma Pivot.add (m:Pivot l C v F)(n:Pivot l D u G): Pivot l (C+D) (v+u) (fun i=> F i+G i) := ⟨ ENNReal.add_ne_top.mpr ⟨m.high,n.high⟩,fun x i=>(m.earns x i).add (n.earns x i) ⟩
lemma Pivot.scale (m:Pivot l C v F) (t:ℝ): Pivot l (‖t‖ₑ*C) (t • v) (fun i=>t • F i):= ⟨ ENNReal.mul_ne_top (by finiteness) m.high, fun x i=>(m.earns x i).scale t ⟩
lemma Pivot.free : Pivot l 0 (0:Packet X r) (fun _=>0):= ⟨ ENNReal.zero_ne_top,fun _ _=> Earn.free ⟩
lemma Earn.sum (I:Finset Z){T:Z→ℝ≥0∞}{v:Z→Packet X r}{F:Z→ W→Packet X r}(m:∀ i∈I,Earn l (T i) (v i) (F i)): Earn l (∑ i∈I,T i) (∑ i∈I,v i) fun w=>∑ i∈I,F i w:=by
 induction I using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; exact Earn.free
 | insert i I h ih=> simp_rw [Finset.sum_insert h]; exact (m _ (by simp)).add (ih fun j hj=> m j ( Finset.mem_insert_of_mem hj ))
lemma Pivot.sum (I:Finset Z){T:Z→ℝ≥0∞}{v:Z→Packet X r}{F:Z→ W→Packet X r}(m:∀ i∈I,Pivot l (T i) (v i) (F i)): Pivot l (∑ i∈I,T i) (∑ i∈I,v i) fun w=> ∑ i∈I,F i w:=by
 induction I using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; exact Pivot.free
 | insert i I h ih=> simp_rw [Finset.sum_insert h]; exact (m _ (by simp)).add (ih fun j hj=> m j (Finset.mem_insert_of_mem hj))
-- rays. exchange. orientation rank-independent via cost.Earn.
lemma Earn.rays (m:Earn l C v F)(n:SplitT l D K U)(i:Fin r): Earn l (C*D) (ray i v K) (fun j=>ray i (F j) (U j)):=by
 let P (K:Layer X X)(v:Packet X r)(z:Tuple X r× X):= v z.1*K z.2 (z.1 i)
 have hm:Earn l (C*D) (P K v) (fun j=>P (U j) (F j)) := m.link (t:=fun x y=>swap K (x i) y) (a:=fun i' x y=> swap (U i') (x i) y) ( fun x=> n.up (x i) ) n.high
 have h (v) (K) : ray i v K=fun z=>∑' y,P K v (exchange i (z,y)):=by
    ext1 x; apply tsum_congr; intro y; unfold swivel; change _= v _*K (x i) (Function.update x i y i); rw [update_self, mul_comm]; rfl -- rw closes?
 simp_rw [h]; exact (hm.pays (exchange i) (exchange i).injective).sumSecond
lemma Pivot.rays (m: Pivot l C v F)(n:SplitT l D K U) (i:Fin r): Pivot l (C*D) (ray i v K) (fun w=> ray i (F w) (U w)):=by
 refine ⟨ ENNReal.mul_ne_top m.high n.high,fun x j=>?_ ⟩; by_cases he:j=i
 · subst j
   let H:=Hold i x
   let q(K:Layer X X)(v:Packet X r)(z:X×Hold i x):=K x z.1*v (update z.2.val i z.1)
   have hp(y:X):= held_change i x y
   have ht:Earn l (D*C) (q K v) (fun w=> q (U w) (F w)):= (n.earns x).link (t:=fun y z=>v ( ( held_change i x y ) z ).val) (a:=fun w y z=>F w ( ( held_change i x y ) z ).val) (fun y=>(m.earns y i).pays (held_change i x y) (held_change i x y).injective) m.high
   have h(v:Packet X r)(K:Layer X X) (z:H): ray i v K z.val=∑' y:X,q K v (y,z):=tsum_congr fun y=> by unfold swivel; rw [show z.val i=x from z.property]
   simp_rw [h]; rw [mul_comm]; exact (ht.pays (Equiv.prodComm _ _) (Equiv.prodComm _ _).injective).sumSecond
 let P (K:Layer X X)(v:Packet X r)(z:Hold j x × X):= v z.1.val * K z.2 (z.1.val i)
 have hm:Earn l (C*D) (P K v) (fun j=>P (U j) (F j)) := (m.earns x j).link (t:=fun x y=>swap K (x.val i) y) (a:=fun i' x y=> swap (U i') (x.val i) y) (fun z=> n.up (z.val i) ) n.high
 have h (v) (K) (z:Hold j x) : ray i v K z.val=∑' y,P K v (exchangeHold x he (z,y)):=by apply tsum_congr; intro y; unfold swivel; change _= v _*K (z.val i) (update z.val i y i); rw [update_self,mul_comm];rfl
 simp_rw [h]; exact (hm.pays (exchangeHold x he) ( exchangeHold x he ).injective).sumSecond
-- renaming & permissions
lemma Pivot.go (m:Pivot l C v F)(u: Equiv.Perm (Fin r)):Pivot l C (v ∘ Tuple.perm X u) (fun i=> F i ∘ Tuple.perm X u):=by
 constructor; exact m.high
 intro x i
 let f:= Equiv.subtypeEquiv (p:=fun z:Tuple X r=> z i=x) (q:=fun z:Tuple X r=> z (u.symm i)=x) (Tuple.perm X u) (by intro z; change z i=x ↔ z (u (u.symm i))=x; rw [u.apply_symm_apply])
 exact (m.earns x _).pays f f.injective
noncomputable abbrev magic (r:ℕ)(C:ℝ≥0∞):= ‖(Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹‖ₑ * (∑ _ : Equiv.Perm (Fin r), C)
lemma Pivot.ways (m:Pivot l C v F): Pivot l (magic r C) (symmetry v) (fun i=> symmetry (F i)):= ( Pivot.sum (Finset.univ (α:=Equiv.Perm (Fin r))) (T:=fun _=>C) (v:=fun u=> v∘ Tuple.perm X u) (F:=fun u i=> F i∘ Tuple.perm X u) (fun u _=> m.go u) ).scale _
lemma Earn.ways (m:Earn l C v F): Earn l (magic r C) (symmetry v) (fun i=>symmetry (F i)) := (Earn.sum (Finset.univ (α:=Equiv.Perm (Fin r))) (T:=fun _=>C) (v:=fun u=> v ∘ Tuple.perm X u) (F:=fun u i=> F i∘ Tuple.perm X u) (fun u _=> m.pays _ (Tuple.perm X u).injective)).scale _
lemma Pivot.drawing (i:List (Fin r))(m:Pivot l C v F)(n:SplitT l D K U) : Pivot l (C*D^i.length) ( Packet.drawing v K i ) ( fun j=> Packet.drawing (F j) (U j) i ) := by
 induction i with | nil=> simpa only [List.length_nil,pow_zero,mul_one,Packet.drawing] using m | cons j i ih=> rw [List.length_cons,pow_succ,← mul_assoc]; exact Pivot.rays ih n _
lemma Earn.drawing (i:List (Fin r))(m:Earn l C v F)(n:SplitT l D K U): Earn l (C*D^i.length) (Packet.drawing v K i) (fun j=>Packet.drawing (F j) (U j) i):=by
 induction i with | nil=> simpa only [List.length_nil,pow_zero,mul_one,Packet.drawing] using m | cons j i ih=> rw [List.length_cons,pow_succ,←mul_assoc]; exact Earn.rays ih n _
lemma Earn.crop (m:Earn l C v F)(e:Y ↪ X): Earn l C (crop e v) (fun i=> crop e (F i)):= m.pays _ (Packet.injectT e)
lemma Earn.offered (m:Earn l C v F)(e:X ↪ Y): Earn l C (offer e v) (fun i=> offer e (F i)):= m.charges _
lemma Pivot.crop (m:Pivot l C v F)(e:Y ↪ X): Pivot l C (crop e v) (fun i=> crop e (F i)):= ⟨m.high,fun x i=> (m.earns (e x) i).pays _ ( Packet.customs e x i ).injective⟩
lemma arrival (v:Packet X r) (e:X ↪ Y) (i:Fin r)(x:X)(z:Hold i (e x)): Stalk.collect (Packet.customs e x i) (fun k: Hold i x=> v k.val) z= offer e v z.val:=by
 let E : Stalk (Packet.customs e x i) z ≃ Stalk (Packet.acrossT e) z.val := {
   toFun:= fun i=>⟨i.val.val,Subtype.ext_iff.mp i.property⟩, invFun:=fun k=>⟨⟨k.val, e.injective ( (congr_fun k.property _).trans z.property )⟩,Subtype.ext k.property⟩, left_inv:=fun _=> rfl, right_inv:= fun _=> rfl }
 exact ( E.tsum_eq (fun i=> v i.val) ).symm.symm
lemma export_miss (v:Packet X r) (e:X ↪ Y) (i:Fin r) (x:Y)(h:x∉Set.range e)(z: Hold i x): offer e v z.val=0:= offer_zero _ (fun ⟨u,h'⟩=> h ⟨ u i,(congr_fun h' _).trans z.property ⟩)
lemma Pivot.offered (m:Pivot l C v F) (e:X ↪ Y) : Pivot l C (offer e v) (fun i=> offer e (F i)) := by
 refine ⟨m.high,fun x i=>?_⟩
 by_cases hx:x∈Set.range e
 · obtain ⟨x,rfl⟩:=hx; simp_rw [← arrival]; exact (m.earns x i).charges _
 simp_rw [export_miss _ e i x hx]; exact Earn.free.scrub zero_le m.high
end YM.RegulatorIR.Budget.FVAAlt2.Wind
