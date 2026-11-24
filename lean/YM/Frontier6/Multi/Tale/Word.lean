import YM.Frontier6.Multi.Tale.Spell

/-!
# Linear reading, including preserving grades under formal extraction

Point-independent roll up a finite filtered field into the common basis
before presenting in future uses. The resulting relations ignored by poll
(a kernel inside the **symbolic** grammar), and that's literally an ideal
on multiplying by any program of exterior readings. Use of poll on true
state comparisons needs geometry safety inspections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Tale
open Function Set Finset Filter Spec
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {V A G' : Type*}[Fintype V][Fintype A]
variable {G:Gauge}{L:Register G}(S:Table L)(T:Table L)
lemma concatenates (x:V→ E4)(v:V→ S.Tag)(y:A→ E4)(u:A→ S.Tag): assembly S (Sum.elim x y) (Sum.elim v u)=assembly S x v * assembly S y u:=by unfold assembly; rw [Fintype.prod_sum_type];rfl
lemma concatenate_many {X:V→Type*}[_h:∀ i,Fintype (X i)](x:∀ i,X i→ E4)(v:∀ i,X i→ S.Tag): assembly S (fun i:(Σ k:V,X k)=>x _ i.snd) (fun i:(Σ k:V,X k)=>v _ i.snd)=∏ i:V,assembly S (x i) (v i):=by unfold assembly; rw [Fintype.prod_sigma]
lemma adds_letter (x:E4)(t:S.Tag)(v:A→ E4)(u:A→S.Tag): letter S x t * assembly S v u=assembly S (fun i:Option A=>i.elim x v) (fun i:Option A => i.elim t u):=by unfold assembly; rw [Fintype.prod_option];rfl
lemma letter_head (x:E4)(t:S.Tag){n:ℕ}(v:Points n)(u:Fin n→S.Tag): letter S x t * assembly S (fun i=>v i) u=assembly S (fun i=>Points.cons x v i) (Fin.cons t u):=by unfold assembly; rw [Fin.prod_univ_succ];rfl
lemma remap (f:V→ E4)(u:V→ S.Tag){n:ℕ}(e:Fin n≃V) (x:Points n) (he:WithLp.ofLp x=f ∘ e)(h:T.Symmetric) : poll S T (assembly S f u) = if Injective f then S.useAt T x (u ∘ e) else 0:=by
    rw [← reorders S e,← he, Tale.examines _ _ h]
    have he:x∈conf n ↔ Injective f:=by
       change Injective x.ofLp ↔ _; rw [he]; exact Equiv.injective_comp e f -- inspect
    simp only [he]

section
variable {C:Family G} {F:Extraction.Order} {S:Table C.book} (K: Final C F S)
variable (x:E4)(d:ℕ)(B:S.Field d)(X:Spelling S)(α:StateIndex K)
set_option quotPrecheck false
local notation "P"=> poll S (state K α)

def Congr (A B: Spelling S) :Prop:= ∀ X α,poll S (state K α) (A*X)=poll S (state K α) (B*X)
lemma almost (A:Spelling S): Congr K A A:=fun _ _=>rfl
lemma Congr.symm {A B:Spelling S}(h:Congr K A B): Congr K B A :=fun i z=> (h i z).symm
lemma Congr.trans {A B C₀:Spelling S}(h:Congr K A B)(e: Congr K B C₀): Congr K A C₀:=fun i x=> (h i x).trans (e i x)
lemma Congr.smul {A B: Spelling S}(h:Congr K A B)(z:ℂ): Congr K (z • A) (z • B):=by intro X p;rw [smul_mul_assoc,smul_mul_assoc,map_smul,map_smul,h X p]
lemma Congr.add {A B X Y:Spelling S}(h:Congr K A B)(e: Congr K X Y): Congr K (A+X) (B+Y):=by intro L p;rw [add_mul,add_mul,map_add,map_add,h L p,e L p]
lemma Congr.right {A B:Spelling S} (h:Congr K A B): Congr K (A*X) (B*X):=by intro Y i;rw [mul_assoc,mul_assoc,h (X*Y)]
lemma Congr.left {A B:Spelling S} (h:Congr K A B):Congr K (X*A) (X*B):= by rw [mul_comm X, mul_comm X]; exact h.right K X
lemma Congr.mul {A B X Y:Spelling S} (h:Congr K A B)(e: Congr K X Y): Congr K (A*X) (B*Y):= (h.right K X).trans K (e.left K B)
lemma Congr.product (s:Finset V){A B:V→Spelling S}(h:∀ i∈s,Congr K (A i) (B i)): Congr K (∏ i∈s,A i) (∏ i∈s,B i):=by
    induction s using Finset.induction_on with
    | empty=> rw [Finset.prod_empty,Finset.prod_empty]; exact almost K 1
    | @insert i s hx ih=> rw [prod_insert hx,prod_insert hx]; exact (h _ (mem_insert_self ..)).mul K (ih (fun i hi=> h _ (mem_insert_of_mem hi)))
lemma Congr.done {A B:Spelling S}(h:Congr K A B): P A=P B:=by simpa only [mul_one] using h 1 α

lemma earnR (p:Spelling S): ∃ L:S.Field d →ₗ[ℂ] ℂ,∀ i:S.Field d,L i=P (letter S x ⟨d,i⟩*p):=by
    induction p using AddMonoidAlgebra.induction_linear with
    | zero=> refine ⟨0,fun _=>?_⟩; simp
    | add a b ha hb=> obtain ⟨v,hv⟩:=ha; obtain ⟨u,hu⟩:=hb; exact ⟨v+u,fun i=> by rw [LinearMap.add_apply,hv,hu,mul_add,map_add]⟩
    | single p z=>
        obtain ⟨n,f,rfl⟩:=exists_enum S p; let Z:= points (Prod.fst ∘ f); let u:=Prod.snd ∘ f; let X':= assembly S (fun i=> Z i) u
        have hp : AddMonoidAlgebra.single (arrange f) z=z • X':=by
           unfold X'; rw [assemble_eq]; unfold press; rw [AddMonoidAlgebra.smul_single]; simp [Z,u] -- eta
        rw [hp]; have hK:=(hierarchy K α).laws.toSymmetric
        by_cases he: Points.cons x Z∈conf (n+1)
        · refine ⟨z • (reading K α x Z u d).toLinearMap,fun i=>?_⟩; unfold X'; rw [mul_smul_comm,map_smul,letter_head,examines S _ hK,if_pos he]; exact congr_arg (z • ·) (reads_at ..)
        refine ⟨0,fun i=>?_⟩; unfold X'; rw [mul_smul_comm,map_smul,letter_head,examines S _ hK,if_neg he,smul_zero]; rfl

def readingMap : S.Field d →ₗ[ℂ] ℂ := (earnR K x d α X).choose
@[simp] lemma reads (x:E4) (X:Spelling S) (b:S.Field d): readingMap K x d X α b=P (letter S x ⟨d,b⟩*X):= (earnR K x d α X).choose_spec b

lemma letter_cap {e:ℕ}(h:d ≤ e): Congr K (letter S x ⟨d,B⟩) (letter S x ⟨e,higher K h B⟩):=by
    intro X α
    induction X using AddMonoidAlgebra.induction_linear with
    | zero=> simp
    | add _ _ ha hb=> rw [mul_add,mul_add,map_add,map_add,ha,hb]
    | single p z=>
        -- scalar times monomial syntax
        obtain ⟨n,f,rfl⟩:=exists_enum S p; let Z:= points (Prod.fst ∘ f); let u:=Prod.snd ∘ f; let Y:= assembly S (fun i=> Z i) u
        have hp : AddMonoidAlgebra.single (arrange f) z=z • Y:=by unfold Y; rw [assemble_eq]; unfold press; rw [AddMonoidAlgebra.smul_single]; simp [Z,u]
        rw [hp]; unfold Y; simp_rw [mul_smul_comm,map_smul,letter_head,examines S _ (hierarchy K α|>.laws.toSymmetric)]; split; next he=>exact congr_arg (z • ·) ((inception K α).kernels h B he u).symm
        next=>rfl
end
end YM.Frontier6.Tale
