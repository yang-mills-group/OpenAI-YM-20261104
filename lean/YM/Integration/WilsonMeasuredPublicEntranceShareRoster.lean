import YM.Integration.WilsonMeasuredPublicEntrancePeerShares
import YM.Integration.WilsonMeasuredPublicEntranceExchange
/-! The ordered compensation is on the original face. Each summand
uses precisely one occupied owner, and one original foreground at every
other member, with its actual sign. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceShareRoster
open Finset WilsonMeasuredPublicEntrancePeerShares
open scoped Classical BigOperators
variable {V:Type*}[DecidableEq V]{K:Type*}[CommRing K]

def pick (p:Share V)(i:V):Bool:=decide ((i,true)∈p.before)
def head (p:Share V)(x e:V→K)(i:V):K:=if pick p i then e i else x i
def field (p:Share V)(x y e:V→K)(i:V):K:=if i∈p.after then y i else head p x e i

omit [DecidableEq V] in
private theorem unique (b:List (V×Bool)) (nd:(b.map Prod.fst).Nodup) {v:V}{c:Bool}
    (found:(v,c)∈b): ((v,true)∈b ↔ c=true):=by
  induction b with
  | nil=>simp at found
  | cons t ts ih=>
    obtain ⟨j,k⟩:=t
    simp only [List.map_cons,List.nodup_cons] at nd
    rcases List.mem_cons.mp found with eq|rest
    · cases eq
      have no:(v,true)∉ts:=fun h=>nd.1 (List.mem_map.mpr ⟨(v,true),h,rfl⟩)
      simp [no,eq_comm]
    · have no:v≠j:=by
        intro eq
        apply nd.1
        exact List.mem_map.mpr ⟨(v,c),rest,eq⟩
      simpa [no] using ih nd.2 rest

private theorem asSet (vs:List V)(nd:vs.Nodup)(a:V→K):(vs.map a).prod=∏i∈vs.toFinset,a i:=by
  induction vs with
  | nil=>simp
  | cons v vs ih=>
    rw [List.nodup_cons] at nd
    have absent:v∉vs.toFinset:=fun h=>nd.1 (List.mem_toFinset.mp h)
    simp [absent,ih nd.2]

theorem original (s:Finset V)(p:Share V)(present:p∈shares s.toList)(x y e:V→K):
    p.atName∈s ∧ peers x y e p=∏i∈s.erase p.atName,field p x y e i:=by
  classical
  let front:=p.before.map Prod.fst
  have layout:front++p.atName::p.after=s.toList:=supports s.toList p present
  have nd:(front++p.atName::p.after).Nodup:=layout ▸ s.nodup_toList
  obtain ⟨nf,nTail,sep⟩:=List.nodup_append.mp nd
  obtain ⟨notAfter,na⟩:=List.nodup_cons.mp nTail
  have notFront:p.atName∉front:=fun h=>sep p.atName h p.atName List.mem_cons_self rfl
  have members(i:V):i∈s ↔ i∈front ∨ i=p.atName ∨ i∈p.after:=by
    rw [← mem_toList,← layout,List.mem_append,List.mem_cons]
  have fields(t:V×Bool)(tB:t∈p.before):field p x y e t.1=(if t.2 then e t.1 else x t.1):=by
    have stored:t.1∈front:=List.mem_map.mpr ⟨t,tB,rfl⟩
    have out:t.1∉p.after:=fun h=>sep t.1 stored t.1 (List.mem_cons_of_mem _ h) rfl
    have typed:=unique p.before nf (show (t.1,t.2)∈p.before from tB)
    cases t with
    | mk i b=>cases b <;> simp_all [field,head,pick]
  have frontEq:(front.map (field p x y e)).prod=(p.before.map (fun t:V×Bool=>if t.2 then e t.1 else x t.1)).prod:=by
    congr 1
    dsimp only [front];rw [List.map_map]
    apply List.map_inj_left.mpr;exact fields
  have backEq:(p.after.map (field p x y e)).prod=(p.after.map y).prod:=by
    congr 1
    apply List.map_inj_left.mpr
    intro i h;simp [field,h]
  have fresh:(front++p.after).Nodup:=List.nodup_append.mpr ⟨nf,na,fun i hi j hj=>sep i hi j (List.mem_cons_of_mem _ hj)⟩
  have name:(front++p.after).toFinset=s.erase p.atName:=by
    ext i
    simp only [List.mem_toFinset,List.mem_append,mem_erase,members]
    constructor
    · intro h
      refine ⟨?_,?_⟩
      · rintro rfl;exact h.elim notFront notAfter
      · exact h.elim Or.inl (fun x=>Or.inr (Or.inr x))
    · rintro ⟨ne,h|h|h⟩
      · exact Or.inl h
      · exact False.elim (ne h)
      · exact Or.inr h
  have grouped:=asSet (front++p.after) fresh (field p x y e)
  rw [name,List.map_append,List.prod_append,frontEq,backEq] at grouped
  exact ⟨(members _).mpr (Or.inr (Or.inl rfl)),grouped⟩

omit [DecidableEq V] in
theorem sign (p:Share V):‖weight (fun _=>(1:ℂ)) p‖=1:=by
  dsimp only [weight]
  generalize p.before=xs
  induction xs with
  | nil=>simp
  | cons t xs ih=>
    simp only [List.map_cons,List.prod_cons,norm_mul,ih,mul_one]
    split <;> simp

end YM.Integration.WilsonMeasuredPublicEntranceShareRoster
end
