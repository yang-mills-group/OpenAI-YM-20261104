import Mathlib.Algebra.MonoidAlgebra.Module
import YM.Frontier6.Multi.Seams.Centers

/-!
# Syntax for interleaved, pending, and done operations

The ring is bookkeeping, there is **no multiplicative map to operators here**.
Multiply and *then* read correlations. Read is set to 0 on non-injective monomials,
will only be identified with Table kernels on disjoint positions. Coeff projections
are correlated with their own exterior monomials separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Tale
open Function Set Finset Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {V A G' : Type*}[Fintype V][Fintype A]
variable {G:Gauge}{L:Register G}(S:Table L)(T:Table L)

/- Word with explicit placement; Fin indices not forced for tree programs. -/
abbrev Monomer := E4 × S.Tag
abbrev Blueprint := Multiset (Monomer S)
abbrev Spelling := AddMonoidAlgebra ℂ (Blueprint S)

def arrange (f:V→G') : Multiset G':= Multiset.map f Finset.univ.val -- V'
lemma suggested (s:Finset V) (f:V→G'): (∑ i∈s, ({f i} : Multiset G'))=Multiset.map f s.val:=by
   induction s using Finset.cons_induction with
   | empty=> simp
   | cons i s hi ih=> rw [sum_cons]; rw [Finset.cons_val,Multiset.map_cons,ih,Multiset.singleton_add]
lemma univ_pack (f:V→G'): (∑ i, ({f i}:Multiset G'))=arrange f:= suggested _ _
lemma pack_reorg (e:V≃A)(p:A→G') : arrange (p ∘ e)=arrange p:=by
   simp_rw [← univ_pack,comp_apply]; exact Equiv.sum_comp e (fun i=>( {p i}:Multiset G'))
lemma arrange_unique (p:V→G'): (arrange p).Nodup ↔ Injective p:=by
   unfold arrange; rw [Multiset.nodup_map_iff_inj_on Finset.univ.nodup]; simp [Injective]

-- safe grammar of monomials independently of choice of read.
def Safe (q:Blueprint S):Prop:= (q.map Prod.fst).Nodup
lemma Safe.arrangement (p:V→ Monomer S): Safe S (arrange p) ↔ Injective (Prod.fst ∘ p):=by
    unfold Safe arrange; rw [Multiset.map_map]; exact arrange_unique _
lemma move_map (f:V→Monomer S) (g:A→Monomer S)(he:arrange f=arrange g)(hg:Safe S (arrange g)) :∃ e:V≃A,f=g ∘ e:=by
   have h₁ := (Safe.arrangement S f).1 (he.symm ▸ hg); have h₂:= (Safe.arrangement S g).1 hg; have hf: Injective f:= fun i j h=> h₁ (congr_arg Prod.fst h); have hg:Injective g:= fun i j h=> h₂ (congr_arg Prod.fst h)
   have hV (i:V): ∃ a:A,g a=f i:=by
        have h:= Multiset.mem_map.mp (he ▸ Multiset.mem_map.mpr ⟨i, mem_univ i,rfl⟩ : f i∈ arrange g); exact ⟨h.choose,h.choose_spec.2⟩ -- type cast issue
   choose y hy using hV; have ht:Surjective y:=by
       intro a; obtain ⟨i,hu,h⟩:= Multiset.mem_map.mp (he.symm ▸ Multiset.mem_map.mpr ⟨a,mem_univ a, rfl⟩ : g a∈arrange f); exact ⟨i,hg ((hy i).trans h)⟩
   have hi:Injective y:= fun i j hz=> hf ((hy i).symm.trans ((congr_arg g hz).trans (hy j)))
   exact ⟨Equiv.ofBijective y ⟨hi,ht⟩, funext fun i=>(hy i).symm⟩
lemma exists_enum (q:Blueprint S):∃ (n:ℕ)(p:Fin n→Monomer S), arrange p=q:=by
    induction q using Multiset.induction with
    | empty=> refine ⟨0,fun i=>Fin.elim0 i,?_⟩; simp only [←univ_pack, univ_eq_empty,Finset.sum_empty]
    | cons a p h=> obtain ⟨n,v,rfl⟩:=h; refine ⟨n+1, Fin.cons (α:=fun _=>Monomer S) a v,?_⟩; simp only [← univ_pack,Fin.sum_univ_succ,Fin.cons_succ,Fin.cons_zero,Multiset.singleton_add]

def Read {n:ℕ}(p:Fin n→Monomer S):= if h : Injective (Prod.fst ∘ p) then S.useAt T (points (Prod.fst ∘ p)) (Prod.snd ∘ p) else 0
lemma Read_perm (h:T.Symmetric){n m:ℕ}(e:Fin n≃ Fin m)(p:Fin m→ Monomer S): Read S T (p ∘ e)=Read S T p:=by
   obtain rfl:n=m:= by simpa using Fintype.card_congr e
   by_cases hg: Injective (Prod.fst ∘ p)
   · have hv:Injective (Prod.fst ∘ (p ∘ e)):=hg.comp e.injective; rw [Read,dif_pos hv,Read,dif_pos hg]; exact S.class_perm _ h e (x:=points (Prod.fst ∘ p)) hg (Prod.snd∘p)
   unfold Read; rw [dif_neg hg,dif_neg (fun hv=> hg ?_)]
   intro i j he; obtain ⟨i,rfl⟩:= e.surjective i; obtain ⟨j,rfl⟩:= e.surjective j; exact congr_arg e (hv he)
lemma same_read (h:T.Symmetric){n m:ℕ}{p:Fin n→Monomer S}{q:Fin m→Monomer S}(he:arrange p=arrange q): Read S T p=Read S T q:=by
   by_cases hx:Safe S (arrange q)
   · obtain ⟨E,hp⟩:= move_map S p q he hx; rw [hp,Read_perm S T h]
   unfold Read; rw [dif_neg (fun hh=>hx ((Safe.arrangement S p|>.2 hh) |> (he ▸ ·))),dif_neg (fun hh=>hx (Safe.arrangement S q|>.2 hh))]

-- evaluation. implicitly zero on multiset words with duplicates

def taste (p:Blueprint S):= Read S T ((exists_enum S p).choose_spec.choose)
def press (p:Blueprint S) (z:ℂ): Spelling S:= AddMonoidAlgebra.single p z
def letter (p:E4)(v:S.Tag) : Spelling S:= press S {(p,v)} 1

def poll : Spelling S →ₗ[ℂ] ℂ :=
   Finsupp.linearCombination ℂ (taste S T) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
@[simp] lemma probe (p:Blueprint S) (z:ℂ): poll S T (press S p z)=z*taste S T p:= Finsupp.linearCombination_single ..
lemma casting (h:T.Symmetric){n:ℕ}(p:Fin n→Monomer S): taste S T (arrange p)=Read S T p:= same_read S T h ((exists_enum S _).choose_spec.choose_spec)

lemma merge (p q:Blueprint S)(z w:ℂ): press S p z*press S q w=press S (p+q) (z*w):= AddMonoidAlgebra.single_mul_single ..
def assembly (f:V→ E4)(v:V→ S.Tag): Spelling S:=∏ i:V, letter S (f i) (v i)
lemma assemble_eq (f:V→ E4)(v:V→S.Tag): assembly S f v=press S (arrange (fun i=>(f i,v i))) 1:=by
   unfold assembly letter press
   rw [AddMonoidAlgebra.prod_single]; rw [univ_pack]; simp
lemma examines (h:T.Symmetric){n:ℕ}(x:Points n)(v:Fin n→ S.Tag): poll S T (assembly S (fun i=>x i) v) = if x∈ conf n then S.useAt T x v else 0:=by
   rw [assemble_eq,probe,casting _ _ h,one_mul]; unfold Read; split; next hx=> exact (if_pos (show x∈conf n from hx)|>.symm)
   next hx=> exact (if_neg (show x∉conf n from hx)|>.symm)
lemma reorders (e:V≃ A)(f:A→ E4)(v:A→S.Tag): assembly S (f ∘ e) (v ∘ e)=assembly S f v:= Equiv.prod_comp e (fun i=>letter S (f i) (v i))
end YM.Frontier6.Tale
