import YM.Integration.WilsonMeasuredPublicEntranceRegisteredExchange
/-! Finite signed expansion of the compensating owner contribution. Every
cofactor consists of unaltered returned lamps, real canonical heads and real
signed canonical heads. Its supports occur once in the original order. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePeerShares
open WilsonMeasuredPublicEntranceCheapOrder
variable {V K:Type*}
structure Share (V:Type*) where
  before:List (V×Bool)
  atName:V
  after:List V

def occupy (v:V) (takeZ:Bool)(p:Share V):Share V:={p with before:=(v,takeZ)::p.before}
def shares : List V → List (Share V)
  | []=>[]
  | v::vs=> ⟨[],v,vs⟩::(shares vs).map (occupy v false)++(shares vs).map (occupy v true)

theorem supports (vs:List V) (p:Share V) (hp:p∈ shares vs):
    p.before.map Prod.fst ++ p.atName :: p.after=vs:=by
  induction vs generalizing p with
  | nil=>simp [shares] at hp
  | cons v vs ih=>
    simp only [shares,List.cons_append,List.mem_cons,List.mem_append,List.mem_map] at hp
    rcases hp with rfl|h|h
    · simp
    · obtain ⟨q,h,rfl⟩:=h
      simpa [occupy] using congrArg (List.cons v) (ih q h)
    · obtain ⟨q,h,rfl⟩:=h
      simpa [occupy] using congrArg (List.cons v) (ih q h)

variable [CommRing K]

def weight (z:V→K)(p:Share V) :K :=
  (p.before.map fun (v,b)=>if b then -z v else 1).prod

def peers (x y e:V→K)(p:Share V):K :=
  (p.before.map fun (v,b)=>if b then e v else x v).prod*(p.after.map y).prod

def signed (x y e z h:V→K)(p:Share V):K :=weight z p*(h p.atName*peers x y e p)

theorem quiet (x y e z h:V→K)(v:V)(p:Share V):
    signed x y e z h (occupy v false p)=x v*signed x y e z h p:=by
  simp [signed,peers,weight,occupy];ring

theorem changed (x y e z h:V→K)(v:V)(p:Share V):
    signed x y e z h (occupy v true p)=(-z v*e v)*signed x y e z h p:=by
  simp [signed,peers,weight,occupy];ring

theorem original (x y e z h:V→K)(vs:List V):
    route y (fun v=>x v-z v*e v) h vs=((shares vs).map (signed x y e z h)).sum:=by
  induction vs with
  | nil=>simp [route,shares]
  | cons v vs ih=>
    simp only [route,ih,shares,List.cons_append,List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_map]
    have one : signed x y e z h ∘ occupy v false = fun t=>x v*signed x y e z h t:=funext (quiet x y e z h v)
    have two : signed x y e z h ∘ occupy v true = fun t=>(-z v*e v)*signed x y e z h t:=funext (changed x y e z h v)
    rw [one,two,List.sum_map_mul_left,List.sum_map_mul_left]
    simp only [signed,weight,peers,List.map_nil,List.prod_nil,one_mul]
    ring

end YM.Integration.WilsonMeasuredPublicEntrancePeerShares
end
