import YM.Frontier6.Multi.Diff.Coast

/-! comparable power forest condensation at many destinations. Keep selected
    horizon coercions distinct from location propagation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road.Fork
open Function Filter Finset Set Spec Fareway Tale Lattice Next.Extract Cells MergeProof.Acme
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I V:Type} [Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}
variable {O:V→Type} [heO:∀ i,Fintype (O i)][htO:∀ i,DecidableEq (O i)]
variable (K:Final C F S)
set_option quotPrecheck false
local notation "σ'"=> (Σ v:V,O v)

-- centers by absolute position, unrelated to grouping root coordinates
variable (u:(Sigma O) →  E4)(c:V→ E4)(v:(Sigma O) →  S.Tag)(J:ℕ)
def pickup (u:(Sigma O) →  E4)(c:V→ E4) : (Sigma O) →  E4:= fun i=> u i + c i.fst
def cutTo {X:Type*}(i:V)(p:(Sigma O) → X):= p ∘ Sigma.mk i

def seedling (i:V) : Spelling S:= assembly S (cutTo i u) (cutTo i v)
def giving (i:V):Spelling S:= assembly S (cutTo i (pickup u c)) (cutTo i v)
def abroad (i:V): S.Field J:=absorb K 0 J (seedling u v i)
def packing (i:V) : Spelling S:= letter S (c i) ⟨J, abroad K u v J i⟩
def combining : Spelling S:= (assembly S (pickup u c) v)-(∏ i:V, packing K u c v J i)
lemma collecting : assembly S (pickup u c) v=∏ i:V, giving u c v i:=by unfold giving assembly; rw [Fintype.prod_sigma]; rfl
lemma giving_at (i:V): giving u c v i=assembly S (fun j=>cutTo i u j+c i) (cutTo i v):= rfl
lemma combining_eq : combining K u c v J=(∏ i:V,giving u c v i)-(∏ i:V,packing K u c v J i):=by unfold combining; rw [collecting]
lemma cost_center (i:V): abroad K u v J i= absorb K (c i) J (giving u c v i):=(throughShift K J _ _).symm
lemma spectrum : ∑ i:V, wages (cutTo i v)=wages v:=by unfold wages expenses; rw [Fintype.sum_sigma];rfl
-- payroll qualification. telescoping using inserting, keeping width test constants
section
variable {T:Fareway I}{x:I→ (Sigma O) →  E4} {uC:I→ V→ E4} {a b:ℝ}{k:I→ℕ}{ξ:Ultrafilter (ℕ×ℕ)}
variable (s:I→ StateIndex K)
lemma buds (A B: V→ BasisRay S I){u:V→ℝ}{a:ℝ} {r:V→ I→ℕ}(he:∀ i,Permit K T ξ k (r i) (A i) (u i))(hh:∀ i,Permit K T ξ k (r i) (B i) (u i))(hf:∀ j,Permit K T ξ k (r j) (fun i x=> A j i x-B j i x) (u j-a))
    (hB:∀ (A: V→ BasisRay S I)(u:V→ℝ), (∀ i,Permit K T ξ k (r i) (A i) (u i))→ T.Costs (fun i=> poll S (state K (s i)) (∏ v:V, A v i (uC i v))) (∑ v:V,u v))
    : T.Costs (fun i=> poll S (state K (s i)) ((∏ v:V,A v i (uC i v)) - (∏ v:V,B v i (uC i v)))) ((∑ v,u v)-a):=by
    let X(v)(i:I):= A v i (uC i v); let Y(v)(i:I):=B v i (uC i v); let Z(U:Finset V)(v:V):= if v∈ U then A v else B v; let f(U)(j):=∏ i:V,Z U i j (uC j i); let h:= (∑ v,u v)-a
    have hz(U:Finset V): T.Costs (fun i=> poll S (state K (s i)) (f U i-f ∅ i)) h:=by
        induction U using Finset.induction_on with
        | empty=> simp only [sub_self,map_zero]; exact Costs.free
        | @insert i U hp ih=>
            let Z' := Function.update (Z U) i (fun j x=>A i j x-B i j x); let u':=Function.update u i (u i-a); have hI(l: V): Permit K T ξ k (r l) (Z' l) (u' l):=by
                by_cases hk:l=i
                · rw [hk]; unfold u' Z'; simp only [Function.update_self]; exact hf _
                unfold u' Z'; simp only [Function.update_of_ne hk]; unfold Z; split; exact he _; exact hh _
            have hu:∑ v,u' v=h:=by
                unfold h; rw [← add_sum_erase Finset.univ u (mem_univ i),← add_sum_erase Finset.univ u' (mem_univ i), sum_congr (s₂:=Finset.univ.erase i) (f:=u') (g:=u) rfl (fun j hj=> update_of_ne (ne_of_mem_erase hj) ..)]; unfold u'; rw [update_self]; ring
            have hQ: T.Costs (fun j=> poll S (state K (s j)) (f (insert i U) j-f U j)) h:=by
               apply (by rw [←hu]; exact hB Z' u' hI : T.Costs (fun j=> poll S (state K (s j)) (∏ v:V,Z' v j (uC j v))) h).cf; filter_upwards with j; congr 1
               unfold f; let W(v):= Z U v j (uC j v); let p(v):= Z (insert i U) v j (uC j v); let x(v):= Z' v j (uC j v)
               have hP(k)(he:k≠i): p k=W k:=by unfold p W Z; simp only [Finset.mem_insert,he,false_or]
               have hX : x i=A i j (uC j i)-W i:=by unfold x W Z' Z; rw [update_self]; simp only [if_neg hp]
               change (∏ v,x v) = (∏ v,p v) - ∏ v,W v; rw [←mul_prod_erase Finset.univ x (mem_univ i),← mul_prod_erase Finset.univ p (mem_univ i),← mul_prod_erase Finset.univ W (mem_univ i), prod_congr rfl (g:=W) (f:=p) (fun k hk=> hP _ (ne_of_mem_erase hk)), prod_congr rfl (g:=W) (f:=x) (fun k hk=> (show x _=W _ from (by unfold x Z'; rw [update_of_ne (ne_of_mem_erase hk)]))), hX, show p i= A i j (uC j i) from (by simp only [p,Z,mem_insert_self, if_true]), sub_mul]
            apply (hQ.add ih).cf; filter_upwards with j; rw [← map_add]; congr 1; abel
    refine (hz Finset.univ).cf ?_; filter_upwards with i; simp only [f,Z,Finset.mem_univ,if_true,Finset.notMem_empty,if_false]
end
end YM.Frontier6.Road.Fork
