import YM.OPE.Compatible.Words.Hat
/-!
# Polynomial test degree and scalar IBP. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cloud
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {I J:Type}{i j k r:ℕ}
local notation "V!"=> Module.Dual ℝ E
variable {p q z:E→ℝ}
inductive anthem : ℕ→ (E→ℝ)→ Prop
     | bank (n:ℕ)(a:ℝ): anthem n fun _=> a
     | add {n:ℕ}{f g:E→ℝ}: anthem n f→anthem n g→anthem n (f+g)
     | cons {n:ℕ} (u:Module.Dual ℝ E){f:E→ℝ}:anthem n f→ anthem (n+1) (⇑u*f)
namespace anthem
lemma cost (h:anthem j p):Bond p:=by induction h with
     | bank=> exact Bond.keep _
     | add _ _ ha hb=> exact ha.add hb
     | cons _ _ ht=> exact (Bond.glyph _).mul ht
lemma scale (h:anthem j p)(v:ℝ): anthem j (v • p):=by induction h with
     | bank=> exact anthem.bank _ _
     | add _ _ ha hb=> rw [smul_add]; exact ha.add hb
     | cons a h ih=> rw [← mul_smul_comm]; exact cons a ih
lemma bloat (h:anthem j p) (hp:j≤k): anthem k p:=by induction h generalizing k with
     | bank=> exact anthem.bank ..
     | add _ _ ha hb=> exact (ha hp).add (hb hp)
     | @cons u a f h ih=> cases k with
                           | zero=>omega
                           | succ k=> exact cons a (ih (by omega))
protected lemma times (h:anthem j p)(hp:anthem k q):anthem (j+k) (p*q):=by induction h with
     | bank n u=> exact bloat (hp.scale u) (by omega)
     | add _ _ ha hb=> rw [add_mul]; exact ha.add hb
     | @cons u a f h ih=> rw [mul_assoc, show u+1+k=u+k+1 by omega]; exact anthem.cons a ih
lemma lyric (w:V!) : anthem 1 ⇑w:=by have hp:=anthem.cons w (show anthem 0 (1:E→ℝ) from anthem.bank _ _); rwa [mul_one] at hp
lemma powers (h:anthem j p) (k:ℕ): anthem (j*k) (p^k):=by induction k with
     | zero=>rw [pow_zero]; exact anthem.bank _ _
     | succ k ih=> rw [pow_succ,Nat.mul_succ]; exact ih.times h
lemma total (x:Finset I)(p:I→E→ℝ)(h:∀ i∈x,anthem j (p i)):anthem j (∑ i∈x,p i):=by induction x using Finset.induction_on with
     | empty=> rw [sum_empty]; exact bank _ _
     | insert i x hi ih=>rw [sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma multitude (x:Finset I)(f:I→ℕ)(p:I→E→ℝ)(h:∀ i∈x,anthem (f i) (p i)): anthem (∑ i∈x,f i) (∏ i∈x,p i):=by induction x using Finset.induction_on with
     | empty=> rw [sum_empty,Finset.prod_empty]; exact bank _ _
     | insert i x hi ih=> rw [sum_insert hi,Finset.prod_insert hi]; exact (h i (Finset.mem_insert_self ..)).times (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
protected lemma comp {f:F→ E}(h:anthem j p) (hp:∀ l:V!, anthem k ((⇑l)∘ f)) : anthem (k*j) (p ∘ f):=by induction h with
     | bank=> exact bank ..
     | add _ _ ha hb=> exact ha.add hb
     | @cons n w q H ih=> rw [Nat.mul_succ, Nat.add_comm]; exact (hp w).times ih
protected lemma compLinear (w:F→ₗ[ℝ] E)(h:anthem j p): anthem j (p ∘ w):=by simpa only [one_mul] using! h.comp (fun l=> (show anthem 1 _ from lyric (E:=F) (l.comp w)))
section finite
variable [FiniteDimensional ℝ E]
protected lemma multiline {ι:Type}[Fintype ι](A:ContinuousMultilinearMap ℝ (fun _ : ι=> E) ℝ)(w:ι→F→E)(n:ι→ℕ)(h:∀ i:ι,∀ ℓ:V!,anthem (n i) (fun x:F=>ℓ (w i x))): anthem (∑ i,n i) fun x=> A (fun i=> w i x):=by
    let b:= Module.finBasis ℝ E; let W:= Fin (Module.finrank ℝ E); have hu(x:F): A (fun i=>w i x)= ∑ p:ι→ W,(A (fun i=> b (p i)))*(∏ i,b.coord (p i) (w i x)):=by
        have hv : (fun i=> w i x)=fun i=> ∑ j:W, (b.coord j (w i x)) • b j:=funext fun i=>(b.sum_repr _).symm
        nth_rw 1 [hv]; rw [show A (fun i=> _)= _ from A.map_sum_finset ..]; rw [show Fintype.piFinset (fun _ : ι=> (Finset.univ: Finset W))=Finset.univ from by ext; simp]; apply Finset.sum_congr rfl; intro p _; rw [A.map_smul_univ]; apply mul_comm
    have ht:= total (j:=∑ i,n i) (Finset.univ:Finset (ι→W)) _ fun p _=> (multitude Finset.univ n _ fun i _=> h i (b.coord (p i))).scale (A (fun i=> b (p i))); convert ht using 1; ext1 i; simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.prod_apply] using hu i
end finite
end anthem
end YM.OPE.Cloud
