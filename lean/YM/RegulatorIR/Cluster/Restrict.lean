import YM.RegulatorIR.Cluster.Ito

/-! Restrict identities to partial contraction matrices. This is not a scale
truncation. All slot identities, including Root V, are for arbitrary rank. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Finset Function Budget Budget.Packet Budget.Layer Budget.Tuple Diagram
open scoped Topology BigOperators Classical
variable {X Y:Type}{a r s:ℕ}
namespace Brief
variable (f:X↪Y) {K:Layer Y Y}

def restrictK (K:Layer Y Y): Layer X X:= fun x y=> K (f x) (f y)
def restrictT (V:Rhythm Y): Rhythm X:= fun k e r=> crop f (V k e r)
lemma trim {V:Rhythm Y} (h:Brief a V): Brief a (restrictT f V):=by
 have ht k e r : restrictT f V k e r≠0 → V k e r ≠0:= fun hx he=> hx (by unfold restrictT; rw [he]; rfl)
 refine ⟨fun k e r he=> h.ranks k e r (ht _ _ _ he), ?_, fun k e r=>crop_symm f (V k e r) (h.align k e r)⟩
 obtain ⟨t,H⟩:= h.times;exact ⟨t,fun k e r he=> H _ _ _ (ht _ _ _ he)⟩

def Limited (K:Layer Y Y): Prop:=∀ x y,K x y≠0 → x∈Set.range f ∧ y∈Set.range f
lemma trimmed_loop (T:Packet Y (r+2))(h:Limited f K): crop f (loop T K) = loop (crop f T) (restrictK f K):=by
 let g:= Embedding.prodMap f f
 ext1 z; change loop T K (acrossT f z)=_
 rw [loop,loop, ← g.injective.tsum_eq (f:=fun x=>curve T K (acrossT f z) x) ?_]
 · apply tsum_congr; intro i; change K (f i.1) (f i.2) * T (linked (f ∘ z) (f i.1,f i.2)) = _; rw [← Tuple.map_link (f:X→Y) z i]; rfl
 intro x hx; obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩:= h x.1 x.2 (fun he=> hx (by change curve _ _ _ _=0; rw [curve,he,zero_mul])); exact ⟨(i,j),Prod.ext hi hj⟩
private lemma knits (K:Layer X X)(T:Packet X (r+1))(U:Packet X (s+1))(x:Tuple X r)(y:Tuple X s): knot K T U (Fin.append x y)=∑' i:X, ∑' j:X,T (Fin.cons i x)*(K i j*U (Fin.cons j y)):=by
 rw [knot,splice_at]; apply tsum_congr; intro i; rw [lace,ray, ← tsum_mul_left]; apply tsum_congr; intro j
 rw [swivel,Fin.cons_zero]; apply congr_arg; apply congr_arg; apply congr_arg; funext a; induction a using Fin.cases <;> simp
lemma trim_knot (T:Packet Y (r+1))(U:Packet Y (s+1))(h: Limited f K): crop f (knot K T U) = knot (restrictK f K) (crop f T) (crop f U):=by
 ext1 z
 rw [← Tuple.recombine z];let x:=cutLeft (s:=s) z;let y:=cutRight (r:=r) z
 change knot K T U (f ∘ Fin.append x y)=knot _ _ _ (Fin.append x y); rw [comp_append, knits,knits]
 rw [← f.injective.tsum_eq]; apply tsum_congr;intro i; rw [← f.injective.tsum_eq]; apply tsum_congr;intro j
 change T (_: Tuple Y _) * (K (f i) (f j)* U _) = T (f ∘ Fin.cons i x)*(K (f i) (f j) * U (f ∘ Fin.cons j y)); rw [comp_cons, comp_cons]
 · intro v hv; exact (h (f i) v (fun ht=>hv (by dsimp only; rw [ht,zero_mul,mul_zero]))).2
 intro v hv; by_contra! hh; apply hv
 change (∑' j:Y,T (Fin.cons v _) * (K v j*U _))=0
 simp_rw [show ∀ y,K v y=0 from fun y=>Classical.byContradiction (hh ∘ And.left ∘ h v y),zero_mul,mul_zero]; exact tsum_zero
lemma crop_match (T V:Ranked Y) (b:ℕ×ℕ)(h:Limited f K): crop f (matchTwo K T V r b)=matchTwo (restrictK f K) (fun i=>crop f (T i)) (fun i=>crop f (V i)) r b:=by
 unfold matchTwo; split_ifs with hr
 · subst r
   let a:= (((b.1:ℝ)+1)*((b.2:ℝ)+1))
   change a • crop f (symmetry (knot K (T _) (V _)))= a • symmetry (knot (restrictK f K) (crop _ _) (crop _ _)); rw [← trim_knot f _ _ h];apply congr_arg; ext1 z; change symmetry _ (acrossT f z)= symmetry _ z; rw [symmetry_at,symmetry_at]; rfl
 rfl
lemma trim_heat (T:Ranked Y)(h:Limited f K): crop f (heating K T r)=heating (restrictK f K) (fun i=>crop f (T i)) r:=by
 unfold heating; let a:= (r+2:ℝ)*(r+1:ℝ)/2
 change a • crop f (symmetry (loop (T _) K)) = a • symmetry (loop (crop f _) (restrictK f K)); rw [← trimmed_loop f _ h]
 apply congr_arg; ext z; change symmetry _ (acrossT f z)= symmetry _ z; rw [symmetry_at,symmetry_at]; rfl
lemma trim_drift {T V:Rhythm Y}(h:Limited f K):restrictT f (drift K T V)=drift (restrictK f K) (restrictT f T) (restrictT f V):=by
 ext1 k;ext1 e;ext1 r; unfold restrictT drift carry force; simp_rw [crop_sum, crop_match f _ _ _ h]
lemma trim_root {T V:Rhythm Y} (h:Limited f K): restrictT f (Root T V K)=Root (restrictT f T) (restrictT f V) (restrictK f K):=by
 ext1 k;ext1 e;ext1 r
 exact congr_arg₂ (· + ·) (trim_heat (r:=r) f (T k e) h) (congr_fun (congr_fun (congr_fun (trim_drift (T:=T) (V:=V) f h) k) e) r)
end Brief
end YM.RegulatorIR.Cluster

namespace YM.RegulatorIR.Cluster
open Finset Function Budget Budget.Packet Budget.Layer Budget.Tuple Diagram
open scoped Topology BigOperators Classical
variable {X Y:Type}{a b c:ℕ}
namespace Brief
lemma trim_twice (f:X↪Y)(T V:Rhythm Y):restrictT f (composeT T V)=composeT (restrictT f T) (restrictT f V):=by ext1 k;ext1 i;ext1 r; exact crop_twice f T V k i r
lemma trim_add (f:X↪Y)(T V:Rhythm Y):restrictT f (T+V)= restrictT f T+restrictT f V:=rfl
lemma trim_pace (f:X↪Y)(T:Rhythm Y):restrictT f (metron T)=metron (restrictT f T):=rfl

def subF (t: Finset X): (i:t) → X:= fun i=>i
-- convenient embeddings

def tile (t: Finset X) : t ↪ X:=⟨subF t, Subtype.val_injective⟩
lemma immerse {T U:Rhythm X}(t:Finset X) (h:∀ s : Finset X,t⊆s → restrictT (tile s) T=restrictT (tile s) U): T=U:=by
 ext1 i;ext1 j;ext1 r;ext1 z
 let s:=(univ.image z) ∪ t
 let y:Tuple s r:= fun i=>⟨z i,mem_union.mpr (Or.inl (mem_image_of_mem z (mem_univ i)))⟩
 exact congr_fun (congr_fun (congr_fun (congr_fun (h s (subset_union_right ..)) i) j) r) y
lemma drafting {T U : Rhythm X}(h:Brief a T)(hh:Brief b U): metron (composeT T U)=composeT (metron T) U+composeT T (metron U):=by
 apply immerse (t:=∅); intro s _; rw [trim_add,trim_pace,trim_twice,trim_twice,trim_twice,trim_pace,trim_pace]; exact pace (trim _ h) (trim _ hh)
lemma partialK {T U V: Rhythm X} (h:Brief a T)(hh:Brief b U)(hx:Brief c V)(t:Finset X){K:Layer X X}(hs:∀ i j,K i j=K j i)(hm:Limited (tile t) K) : Root (composeT T U) V K=composeT (Root T V K) U+composeT T (Root U V K)+ drift K T U:= by
 apply immerse t; intro s hp
 have he:Limited (tile s) K:=by
    intro x y hu; obtain ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩:= hm x y hu
    exact ⟨⟨⟨i,hp i.property⟩,rfl⟩,⟨⟨j,hp j.property⟩,rfl⟩⟩
 rw [trim_root _ he,trim_add, trim_add,trim_twice,trim_twice,trim_twice,trim_root _ he,trim_root _ he, trim_drift _ he]; exact ito (K:=restrictK (tile s) K) (fun i j=> hs (tile s i) (tile s j)) (trim _ h) (trim _ hh) (trim _ hx)
end Brief
end YM.RegulatorIR.Cluster
