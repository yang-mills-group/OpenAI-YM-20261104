import YM.QCDVacuum.Stall.Chirp
/-! # Product recipes on local sectors. No factory factors on dormant variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus.Fields
open Function Finset
open scoped Topology BigOperators Classical
variable {J I K : Type} [Fintype J] [Fintype I] {P : Type*} [CommSemiring P]
-- total colorings with default a
def field (A:Finset J)(a:I): Finset (J→I) := Fintype.piFinset fun i=> if i∈A then univ else {a}
lemma fields (A:Finset J)(a:I)(c:J→I): c∈field A a ↔ ∀ i,i∉A→c i=a:=by
  simp only [field,Fintype.mem_piFinset]; refine forall_congr' (fun i=>?_); by_cases hi:i∈A<;>simp [hi]
lemma produce (A:Finset J)(a:I)(c:J→I→P): ∏ i∈A,∑ j,c i j=∑ s∈field A a, ∏ i∈A,c i (s i):=by
  let f (i:J):= if i∈A then c i else fun _=>1
  let g(i:J):= if i∈A then (univ:Finset I) else {a}
  calc
    _ = ∏ i, ∑ j∈g i,f i j := by
      rw [← prod_mul_prod_compl A]; rw [show (∏ i∈Aᶜ,∑ j∈g i, f i j)=1 from prod_eq_one fun i hi=>by simp [g,f,(mem_compl.mp hi)],mul_one]; exact prod_congr rfl fun i hi=>by simp [f,g,hi]
    _ = _:= by
      rw [Finset.prod_univ_sum]; apply sum_congr rfl; intro i _
      rw [← prod_mul_prod_compl A]; rw [show (∏ j∈Aᶜ, f j (i j))=1 from prod_eq_one fun j hj=>by simp [f,mem_compl.mp hj],mul_one]; exact prod_congr rfl fun j hj=>by simp [f,hj]
lemma harvest (A:Finset K)(q:K→Finset J)(d:(A:Set _).PairwiseDisjoint q)(a:I)(c:K→(J→I)→P)
    (h:∀i∈A,∀ f g,(∀ j∈q i,f j=g j)→c i f=c i g):
    ∏ i∈A, ∑ j∈field (q i) a,c i j= ∑ j∈ field (A.biUnion q) a,∏ i∈A,c i j:=by
  let D(t:J→I)(x:K):=(fun j=> if j∈q x then t j else a)
  rw [Finset.prod_sum]; refine Eq.symm (Finset.sum_bij (fun x _ i _=> D x i) ?hm ?inj ?sur ?val)
  case hm=> intro b hb; refine mem_pi.mpr fun i hi=>?_ ; exact (fields ..).2 (fun j hj=> if_neg hj)
  case inj=>
    intro i hi j hj he; funext b; by_cases hc:b∈ A.biUnion q
    swap; · exact ((fields ..).1 hi b hc).trans ((fields ..).1 hj b hc).symm
    obtain ⟨u,hx,hy⟩:=mem_biUnion.mp hc; have hp : D i u b=D j u b:= congr_arg (fun (f:(x:K)→x∈A→J→I)=> f u hx b) he
    simpa only [D,if_pos hy] using hp
  case val=> intro i _; rw [← prod_attach]; apply Finset.prod_congr rfl; exact fun j _=> h j.val j.prop _ _ (fun k hk=> (if_pos hk).symm) -- RHS shape test
  case sur=>
    intro w hw
    have ht:∀ j∈ A.biUnion q,∃ i∈A,j∈q i:=fun _ hi=> mem_biUnion.mp hi
    let s (j:J) := if hx:j∈A.biUnion q then w (ht j hx).choose (ht j hx|>.choose_spec.1) j else a
    refine ⟨s,(fields ..).2 (fun i hi=>dif_neg hi),?_⟩; funext i hi j; by_cases hv:j∈ q i
    swap; · exact (if_neg hv).trans ((fields ..).1 (mem_pi.mp hw _ hi) j hv).symm -- HEq?
    have hm : j∈ A.biUnion q:= mem_biUnion.mpr ⟨i,hi,hv⟩
    change D _ i j=_; unfold D s; rw [if_pos hv,dif_pos hm]
    have he : (ht j hm).choose=i:= by by_contra hn; exact disjoint_left.mp (d (ht j hm|>.choose_spec.1) hi hn) (ht j hm|>.choose_spec.2) hv
    simp only [he] -- dep rw
end YM.PhysicalNext.Repeat.Lotus.Fields
