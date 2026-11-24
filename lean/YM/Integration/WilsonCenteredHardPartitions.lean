import YM.Integration.WilsonCenteredCompulsoryPair

/-! The absolute mixed hard face on a complete original admissible
collection, with both distinct hard owners retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredHardPartitions
open Finset Marker
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    (a b c : V) (M : R.Mode) (apart : a≠b) (pair : M.val={a,b})

def face (X : Poly R) := X.part M-X.part (R.fire c)

include apart pair
theorem multiply (X Y : Poly R) : face c M (X*Y)=
    face c M X*Y.part R.quiet + X.part R.quiet*face c M Y+
      X.part (R.fire a)*Y.part (R.fire b)+X.part (R.fire b)*Y.part (R.fire a) := by
  have hot : M ≠ R.quiet := by
    intro h
    have yes : a∈M.val:=by rw [pair];simp
    rw [h] at yes
    exact notMem_empty _ yes
  let z : ℂ := X.part R.quiet-1
  let A : Poly R := X-z•1
  have aq : A.part R.quiet=1 := by
    change X.part R.quiet - z*(1:Poly R).part R.quiet=1
    simp [z]
  have fresh (j : R.Mode) (live : j≠R.quiet) : A.part j=X.part j := by
    change X.part j-z*(1:Poly R).part j=_
    simp [Poly.one_part,live]
  have XY : X*Y=A*Y+z•Y := by
    have back : A+z•1=X:=sub_add_cancel _ _
    calc
      _=(A+z•1)*Y:=congrArg (fun t : Poly R=>t*Y) back.symm
      _=_:=by rw [add_mul,smul_mul_assoc,one_mul]
  have old:=WilsonCenteredCompulsoryPair.original a b c M apart pair A 1 Y aq (by simp)
  simp only [one_mul,Poly.one_part,if_neg hot,if_neg (R.fire_hot _),sub_zero,
    fresh M hot,fresh _ (R.fire_hot _)] at old
  rw [face,XY]
  simp only [Poly.part_plus,Poly.part_smul,face,z]
  linear_combination old

def booked {J : Type*} [DecidableEq J] (f : J→Poly R) (S : Finset J) :=
  ∑ i∈S,face c M (f i)*∏j∈S.erase i,(f j).part R.quiet

def separate {J : Type*} [DecidableEq J] (f : J→Poly R) (S : Finset J) :=
  ∑ i∈S,(f i).part (R.fire a)*(∏j∈S.erase i,f j).part (R.fire b)

theorem collection {J : Type*} [DecidableEq J] (f : J→Poly R) (S : Finset J) :
    face c M (∏i∈S,f i)=booked c M f S+separate a b f S := by
  have hot : M≠R.quiet := by
    intro e;have h : a∈M.val:=by rw [pair];simp
    exact notMem_empty _ (e ▸ h)
  induction S using Finset.induction_on with
  | empty=>simp [face,booked,separate,hot,R.fire_hot]
  | @insert i S outside prior=>
    rw [prod_insert outside,multiply a b c M apart pair,prior]
    let q := (f i).part R.quiet
    let va := (f i).part (R.fire a)
    let vb := (f i).part (R.fire b)
    have expand (j : J) (hj : j∈S) :
        (insert i S).erase j = insert i (S.erase j) :=
      erase_insert_of_ne (show i≠j by rintro rfl;exact outside hj)
    have first : booked c M f (insert i S) =
        face c M (f i)*(∏j∈S,(f j).part R.quiet)+q*booked c M f S := by
      unfold booked
      rw [sum_insert outside,erase_insert outside,mul_sum]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [expand j hj,prod_insert (fun e=>outside (mem_of_mem_erase e))]
      ring
    have second : separate a b f (insert i S) =
        va*(∏j∈S,f j).part (R.fire b)+q*separate a b f S+
          vb*(∏j∈S,f j).part (R.fire a) := by
      unfold separate
      rw [sum_insert outside,erase_insert outside,Multi.first_of_prod S f a,mul_sum,mul_sum,add_assoc,←sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [expand j hj,prod_insert (fun e=>outside (mem_of_mem_erase e)),Multi.first_mul,Multi.quiet_of_prod]
      dsimp [q,vb];ring
    rw [first,second,Multi.quiet_of_prod]
    dsimp [q,va,vb];ring

end YM.Integration.WilsonCenteredHardPartitions
