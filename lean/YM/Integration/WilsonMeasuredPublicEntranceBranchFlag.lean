import YM.Integration.WilsonPhysicalUnitaryFiltration

/-! The directed part of a bidegree matrix that detects a nontrivial finite-order action. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceBranchFlag
open Finset
open scoped Classical BigOperators
variable {I E:Type*}[Fintype I][AddCommGroup E][Module ℂ E]

def inspected (w:I→ℕ×ℕ)(i j:I):Prop :=
  (w i).1=(w j).1 ∧ (w j).2≤(w i).2

private def rank (w:I→ℕ×ℕ)(i:I):ℕ:=(w i).1*((univ.sup fun j=>(w j).2)+1)+(w i).2

private theorem split (w:I→ℕ×ℕ)(i j:I)(h:rank w j≤rank w i):
    (w j).1<(w i).1 ∨ inspected w i j:=by
  let B:=univ.sup fun k=>(w k).2
  have cap:(w i).2≤B:=le_sup (f:=fun k=>(w k).2) (mem_univ i)
  change (w j).1*(B+1)+(w j).2≤(w i).1*(B+1)+(w i).2 at h
  by_cases lower:(w j).1<(w i).1
  · exact Or.inl lower
  have eq:(w i).1=(w j).1:=by
    apply le_antisymm (Nat.le_of_not_gt lower)
    by_contra! bad
    have bound:=Nat.mul_le_mul_right (B+1) (Nat.succ_le_of_lt bad)
    rw [Nat.succ_mul] at bound
    omega
  exact Or.inr ⟨eq,by rw [eq] at h;omega⟩

/-- Coordinates are output first, input second. The whole repeated bidegree block is tested. -/
theorem nilpotent (basis:Module.Basis I ℂ E)(w:I→ℕ×ℕ)(A:Module.End ℂ E)
    (grade:∀i j,(w j).1<(w i).1→basis.coord i (A (basis j))=0)
    (tested:∀i j,inspected w i j→basis.coord i (A (basis j))=0):IsNilpotent A:=by
  have lowers(i j:I)(h:rank w j≤rank w i):basis.coord i (A (basis j))=0:=
    (split w i j h).elim (grade i j) (tested i j)
  have vanish(k:ℕ)(i j:I)(h:rank w j<rank w i+k):basis.coord i ((A^k) (basis j))=0:=by
    induction k generalizing i j with
    | zero =>
      have ne:j≠i:=by intro e;subst i;omega
      simp [Module.Basis.coord_apply,ne]
    | succ k ih =>
      rw [pow_succ,Module.End.mul_apply,←basis.sum_repr (A (basis j)),map_sum,map_sum]
      apply Finset.sum_eq_zero
      intro t _
      by_cases short:rank w t<rank w i+k
      · simp only [map_smul,smul_eq_mul,ih i t short,mul_zero]
      · have z:basis.repr (A (basis j)) t=0:=lowers t j (by omega)
        simp only [z,zero_smul,map_zero]
  let N:=univ.sup (rank w)+1
  refine ⟨N,basis.ext fun j=>?_⟩
  apply basis.repr.injective
  ext i
  simp only [LinearMap.zero_apply,map_zero,Finsupp.zero_apply]
  change basis.coord i ((A^N) (basis j))=0
  have h:rank w j≤univ.sup (rank w):=le_sup (f:=rank w) (mem_univ j)
  exact vanish N i j (by dsimp [N];omega)

variable {X:Type*}[AddCommGroup X][Module ℂ X]

private theorem collapse (T:Module.End ℂ X)(nil:IsNilpotent (T-1))
    (cancel:∀x,(T-1) ((T-1) x)=0→(T-1) x=0):T=1:=by
  let A:Module.End ℂ X:=T-1
  have down(k:ℕ)(x:X)(h:(A^k) x=0):A x=0:=by
    induction k generalizing x with
    | zero =>
      have eq:x=0:=by simpa only [pow_zero,Module.End.one_apply] using h
      rw [eq,map_zero]
    | succ k ih =>exact cancel x (ih (A x) (by simpa only [pow_succ,Module.End.mul_apply] using h))
  obtain ⟨k,h⟩:=nil
  exact LinearMap.ext fun x=>sub_eq_zero.mp (show T x-x=0 from down k x (by rw [show A^k=0 from h];rfl))

theorem finite_order (T:Module.End ℂ X)(nil:IsNilpotent (T-1)){n:ℕ}(hn:0<n)(period:T^n=1):T=1:=by
  apply collapse T nil
  let A:Module.End ℂ X:=T-1
  have near(x:X):T x=x+A x:=by change T x=x+(T x-x);abel
  intro x hx
  change A (A x)=0 at hx
  have fixed:T (A x)=A x:=by rw [near (A x),hx,add_zero]
  have linear(k:ℕ):(T^k) x=x+(k:ℂ)•A x:=by
    induction k with
    | zero =>simp
    | succ k ih =>
      rw [pow_succ',Module.End.mul_apply,ih,map_add,map_smul,fixed,near x,Nat.cast_succ,add_smul,one_smul]
      abel
  have z:=linear n
  rw [period,Module.End.one_apply] at z
  have paid:(n:ℂ)•A x=0:=add_left_cancel (a:=x) (by simpa only [add_zero] using z.symm)
  exact (smul_eq_zero.mp paid).resolve_left (by exact_mod_cast hn.ne')

/-- A positive real quadratic reading gives the same collapse on an actual measured limit. -/
theorem measured (T:Module.End ℂ X)(nil:IsNilpotent (T-1))(mass:X→ℝ)
    (positive:∀x:X,x≠0→0 < mass x)
    (parallelogram:∀x y,mass (x+y)+mass (x-y)=2*(mass x+mass y))
    (keeps:∀x,mass (T x)=mass x):T=1:=by
  apply collapse T nil
  let A:Module.End ℂ X:=T-1
  have near(x:X):T x=x+A x:=by change T x=x+(T x-x);abel
  intro x hx
  change A (A x)=0 at hx
  have fixed:T (A x)=A x:=by rw [near (A x),hx,add_zero]
  have back:T (x-A x)=x:=by rw [map_sub,fixed,near x,add_sub_cancel_right]
  by_contra bad
  have plus:=keeps x
  have minus:=keeps (x-A x)
  rw [near x] at plus
  rw [back] at minus
  linarith only [plus,minus,parallelogram x (A x),positive (A x) bad]

end YM.Integration.WilsonMeasuredPublicEntranceBranchFlag
