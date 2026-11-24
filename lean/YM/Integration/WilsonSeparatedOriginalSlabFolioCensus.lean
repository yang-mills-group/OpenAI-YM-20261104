import YM.Integration.WilsonSeparatedOriginalSlabRegentPortfolio

/-! Index every entry in the actual finite list of each admissible parent, retaining multiplicities including repeated tests. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFolioCensus
open Finset
open scoped Classical BigOperators
variable {Y M:Type*}[AddCommMonoid M]{T:Y → Type*}

abbrev Slots (A:Finset Y)(L:(y:Y) → List (T y)):=Σ y:{y//y∈A},Fin (L y.val).length

def member {A:Finset Y}{L:(y:Y) → List (T y)}(i:Slots A L):T i.1.val:=(L i.1.val).get i.2

theorem entries {A:Finset Y}{L:(y:Y) → List (T y)}(i:Slots A L):member i∈L i.1.val:=List.get_mem _ _

theorem list {α:Type*}(l:List α)(f:α → M): (l.map f).sum=∑i:Fin l.length,f (l.get i):=by
  nth_rw 1 [←List.ofFn_get l]
  rw [List.map_ofFn,List.sum_ofFn];rfl

theorem sums (A:Finset Y)(L:(y:Y) → List (T y))(f:(y:Y) → T y → M):
    ∑i:Slots A L,f i.1.val (member i)=∑y∈A,((L y).map (f y)).sum:=by
  rw [Fintype.sum_sigma]
  calc ∑y:{y//y∈A}, ∑i:Fin (L y.val).length,f y.val ((L y.val).get i) =∑y:{y//y∈A},((L y.val).map (f y.val)).sum:=by
         apply Finset.sum_congr rfl;intro y _
         exact (list (L y.val) (f y.val)).symm
    _=_:=(Finset.sum_subtype A (fun y=>Iff.rfl) (fun y=>((L y).map (f y)).sum)).symm

end YM.Integration.WilsonSeparatedOriginalSlabFolioCensus
