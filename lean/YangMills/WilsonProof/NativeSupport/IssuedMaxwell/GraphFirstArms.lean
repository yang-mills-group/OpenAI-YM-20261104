import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphArms
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphFirstArms
open YM Function
open scoped BigOperators Classical
variable {n m:ℕ}{V:Type*}
theorem placed (l:Fin n→V)(r:Fin m→V)(j:Fin n)(z:V):
    Fin.append (update l j z) r=update (Fin.append l r) (Fin.castAdd m j) z:=by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    by_cases same:i=j
    · subst i
      rw [Fin.append_left,update_self,update_self]
    · have apart:Fin.castAdd m i≠Fin.castAdd m j:=by
        intro h
        exact same (Fin.ext (congrArg (fun q:Fin (n+m)=>q.val) h))
      rw [Fin.append_left,update_of_ne same,update_of_ne apart,Fin.append_left]
  · intro i
    have apart:Fin.natAdd n i≠Fin.castAdd m j:=by
      intro h
      have eq:=congrArg Fin.val h
      change n+i.val=j.val at eq
      omega
    rw [Fin.append_right,update_of_ne apart,Fin.append_right]
variable [AddCommGroup V][Module ℂ V]
def held (F:MultilinearMap ℂ (fun _:Fin (n+m)=>V) ℂ)(r:Fin m→V):
    MultilinearMap ℂ (fun _:Fin n=>V) ℂ:=by
  refine MultilinearMap.mk' (fun l=>F (Fin.append l r)) ?_ ?_
  · intro l j x y
    change F (Fin.append (update l j (x+y)) r)=F (Fin.append (update l j x) r)+F (Fin.append (update l j y) r)
    simp only [placed]
    exact F.map_update_add _ _ _ _
  · intro l j c x
    change F (Fin.append (update l j (c • x)) r)=c • F (Fin.append (update l j x) r)
    simp only [placed]
    exact F.map_update_smul _ _ _ _
end IssuedMaxwell.GraphFirstArms
end
