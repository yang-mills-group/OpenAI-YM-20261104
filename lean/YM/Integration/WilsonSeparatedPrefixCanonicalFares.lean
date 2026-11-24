import YM.Integration.WilsonSeparatedPrefixCanonicalPostAdd

/-! Site budgets for a finite sum of separately registered entries. No
neighborhood connecting distinct members of the sum is needed. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalFares
open Function Finset MeasureTheory Lattice Wilson RG Marker MergeProof MergeProof.Accent Push Push.AbsoluteSums
open GridApprox.Nil Ac
open scoped BigOperators Classical
variable {V I Y:Type} [DecidableEq V] {B:Census V} {n:Side} {M:ℕ} {w:V → ℝ} {S:I → Support n} {e:ℝ}

theorem add {a b:ℝ}{f g:I → Y → Poly B} (x:Towed w S f M e a)(y:Towed w S g M e b):
    Towed w S (fun i U=>f i U+g i U) M e (a+b) := by
  obtain ⟨A,ha,sa,la⟩:=x
  obtain ⟨C,hc,sc,lc⟩:=y
  refine ⟨fun i=>A i+C i,ha.add hc,?_,?_⟩
  · intro z
    convert Extra.Multi.Budget.plus (sa z) (sc z) using 1
    funext i
    split_ifs <;> ring
  · intro i
    obtain ⟨F,pos,cap,charge⟩:=la i
    obtain ⟨G,live,hold,due⟩:=lc i
    refine ⟨fun m=>F m+G m,fun m=>add_nonneg (pos m) (live m),?_,?_⟩
    · exact fun U m=>(norm_add_le _ _).trans (add_le_add (cap U m) (hold U m))
    · simpa only [wordsPrice,mul_add,Finset.sum_add_distrib] using add_le_add charge due

theorem scale {a:ℝ}{f:I → Y → Poly B}(x:Towed w S f M e a)(z:ℂ):
    Towed w S (fun i U=>z • f i U) M e (‖z‖*a) := by
  obtain ⟨A,ha,sa,la⟩:=x
  refine ⟨fun i=>‖z‖*A i,ha.mul_left _,?_,fun i=>WilsonSeparatedPrefixCanonicalMixed.loci (la i) z⟩
  intro b
  convert budget_scale (norm_nonneg z) (sa b) using 1
  funext i
  split_ifs <;> ring

theorem add_family {T:Type} [DecidableEq T] (seats:Finset T)
    {f:T → I → Y → Poly B}{g:I → Y → Poly B}{p:T → ℝ}{a:ℝ}
    (posts:∀v∈seats,Towed w S (f v) M e (p v)) (original:Towed w S g M e a):
    Towed w S (fun i U=>(∑v∈seats,f v i U)+g i U) M e ((∑v∈seats,p v)+a) := by
  induction seats using Finset.induction_on with
  | empty=>simpa only [sum_empty,zero_add] using original
  | @insert v t hv ih=>
    have now:=add (posts v (mem_insert_self ..))
      (ih (fun j hj=>posts j (mem_insert_of_mem hj)))
    simpa only [sum_insert hv,add_assoc] using now

end YM.Integration.WilsonSeparatedPrefixCanonicalFares
end
