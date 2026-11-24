import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCover
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphArms
open YM Set Function
open scoped BigOperators Classical
variable {n m:ℕ}{V:Type*}

theorem placed (l:Fin n→V)(r:Fin m→V)(j:Fin m)(z:V):
    Fin.append l (update r j z)=update (Fin.append l r) (Fin.natAdd n j) z:=by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    have apart:i.castAdd m≠Fin.natAdd n j:=by
      intro h
      have eq:=congrArg Fin.val h
      change i.val=n+j.val at eq
      omega
    rw [Fin.append_left,update_of_ne apart,Fin.append_left]
  · intro i
    by_cases same:i=j
    · subst i
      rw [Fin.append_right,update_self,update_self]
    · have apart:Fin.natAdd n i≠Fin.natAdd n j:=by
        intro h
        apply same
        apply Fin.ext
        have eq:=congrArg Fin.val h
        change n+i.val=n+j.val at eq
        omega
      rw [Fin.append_right,update_of_ne same,update_of_ne apart,Fin.append_right]

variable [AddCommGroup V][Module ℂ V]
def held (F:MultilinearMap ℂ (fun _:Fin (n+m)=>V) ℂ)(l:Fin n→V):
    MultilinearMap ℂ (fun _:Fin m=>V) ℂ:=by
  refine MultilinearMap.mk' (fun r=>F (Fin.append l r)) ?_ ?_
  · intro r j x y
    change F (Fin.append l (update r j (x+y)))=F (Fin.append l (update r j x))+F (Fin.append l (update r j y))
    simp only [placed]
    exact F.map_update_add _ _ _ _
  · intro r j c x
    change F (Fin.append l (update r j (c • x)))=c • F (Fin.append l (update r j x))
    simp only [placed]
    exact F.map_update_smul _ _ _ _
end IssuedMaxwell.GraphArms
end
