import YM.Integration.WilsonThermometerWeakPairOrdinary
import YM.OPE.Trees.Association

/-! Re-index the actual tree reading as an ordinary near pair with one independent exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairSeats
open Function Finset Filter Set Table Spec OPE OPE.Arboreal OPE.Prescription
open WilsonThermometerWeakPairFork WilsonThermometerWeakPairRooms
open scoped Classical Topology BigOperators
local notation "bare" => WilsonThermometerWeakPairStage.bare
def tip:Finset (Fin 5):={4}
abbrev Side:=↥tip⊕Fin 0
private def soleSeat:Side≃Unit where
  toFun:=fun _=>()
  invFun:=fun _=>.inl ⟨4,by simp [tip]⟩
  left_inv:=fun j=>by
    rcases j with ⟨a,ha⟩|a
    · have eq:a=4:=by simpa [tip] using ha
      subst a;rfl
    · exact a.elim0
  right_inv:=fun j=>by cases j;rfl

private lemma seated {I V:Type}(f:I→V)(g:Fin 5→V):
    (beside f (sole (g 4))) ∘ Equiv.sumCongr (Equiv.refl I) soleSeat=
      beside f (beside (crop g tip) (bare:Fin 0→V)):=by
  funext o
  rcases o with i|(⟨j,hj⟩|j)
  · rfl
  · have h:j=4:=by simpa [tip] using hj
    subst j;rfl
  · exact j.elim0

variable {G:Gauge}{L:Register G}{S A:Table L}{Q:DiffPlan S}
lemma returned {I:Type}[Fintype I](ha:A.Symmetric)(p:I→L.Token)(x:I→E4)(q:Fin 5→L.Token)(X:Fin 5→E4)
    (hx:Injective (beside x (sole (X 4)))):
    observe A (beside x (beside (crop X tip) (bare:Fin 0→E4)))
      (beside p (beside (crop q tip) (bare:Fin 0→L.Token)))=
      observe A (beside x (sole (X 4))) (beside p (sole (q 4))):=by
  have seen:=OPE.perm_observe A ha (Equiv.sumCongr (Equiv.refl I) soleSeat) (beside p (sole (q 4))) hx
  rwa [seated,seated] at seen

private lemma withEmpty {b:Finset (Fin 5)} {X:Fin 5→E4}(h:Injective (crop X b)):
    Injective (beside (crop X b) (bare:Fin 0→E4)):=by
  refine beside_distinct.mpr ⟨h,fun i=>i.elim0,fun _ j=>j.elim0⟩

lemma full (ha:A.Symmetric)(p:Fin 5→L.Token)(X:Fin 5→E4)
    (hc:Injective (crop X frame.leaves))(hh:Injective (beside (crop X near) (sole (X 4)))):
    whole A frame.leaves X p (bare:Fin 0→E4) bare=
      observe A (beside (crop X near) (sole (X 4))) (beside (crop p near) (sole (p 4))):=by
  have union:near∪tip=frame.leaves:=by rw [leave];decide
  have separate:Disjoint near tip:=by decide
  rw [logs_combine (a:=near) (b:=tip) (c:=frame.leaves) (p:=p) (q:=bare) A ha
    (by ext i;simpa only [Finset.mem_union] using Finset.ext_iff.mp union i) separate (withEmpty hc)]
  exact returned ha (crop p near) (crop X near) p X hh

lemma cut (P:Prescription Q)(ha:A.Symmetric)(p:Fin 5→L.Token)(X:Fin 5→E4)(w:Mode Q)
    (hc:Injective (crop X WilsonThermometerWeakPairRooms.outside))(hh:Injective (beside (sole (X 1)) (sole (X 4)))):
    whole A WilsonThermometerWeakPairRooms.outside X (update p 1 (P.letter w)) (bare:Fin 0→E4) bare=
      observe A (beside (sole (X 1)) (sole (X 4))) (beside (sole (P.letter w)) (sole (p 4))):=by
  have union:insert (1:Fin 5) tip=WilsonThermometerWeakPairRooms.outside:=by decide
  have distinct:(1:Fin 5)∉tip:=by decide
  have ret:=one_combine (p:=p) (w:=w) (q:=bare) (i:=(1:Fin 5)) (b:=tip) (c:=WilsonThermometerWeakPairRooms.outside) A ha P
    (by ext i;simpa only [Finset.mem_insert] using Finset.ext_iff.mp union i) distinct (withEmpty hc)
  refine Eq.trans ?_ (ret.trans ?_)
  · congr 1
    funext i
    by_cases eq:i=1 <;> simp [Function.update,eq]
  · exact returned ha (sole (P.letter w)) (sole (X 1)) p X hh

end YM.Integration.WilsonThermometerWeakPairSeats
end
