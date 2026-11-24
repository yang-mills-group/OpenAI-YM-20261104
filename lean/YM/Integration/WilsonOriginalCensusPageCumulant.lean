import YM.Integration.WilsonOriginalCensusWickPages

/-! Resolve the copies of precisely the occupied inherited pieces before applying
the connected Gaussian functional. The pinned measure and omitted atoms stay fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPageCumulant
open Finset Function Marker Multi Extra.Trajectories Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {V A:Type} [Fintype V] [DecidableEq V] [CommSemiring A] [Algebra ℂ A]
  (R:Census V)(s:R.Mode)(f:A →ₗ[ℂ] ℂ)(unit:f 1=1)

def put (w:s.val → A)(i:V):A:=if h:i∈s.val then w ⟨i,h⟩ else 0

omit [Fintype V] [Algebra ℂ A] in
private theorem changeAt [DecidableEq s.val] (w:s.val → A)(i:s.val)(a:A):
    put R s (update w i a)=update (put R s w) i.val a:=by
  classical
  funext v
  by_cases eq:v=i.val
  · subst v
    simp [put]
  · rw [Function.update_of_ne eq]
    by_cases live:v∈s.val
    · have ne:(⟨v,live⟩:s.val)≠i:=fun e=>eq (congrArg Subtype.val e)
      simp [put,live,ne]
    · simp [put,live]

def invoice : MultilinearMap ℂ (fun _ : s.val => A) ℂ where
  toFun w:=(connected (moments R f (put R s w))).part s
  map_update_add' w i a b:=by
    rw [changeAt,changeAt,changeAt]
    exact cumulant_add f unit (put R s w) i.val i.property a b
  map_update_smul' w i a b:=by
    rw [changeAt,changeAt]
    exact cumulant_smul f unit (put R s w) i.val i.property b a

include unit in
theorem resolved {L:Type} [Fintype L](slot:V → L → A):
    (connected (moments R f (fun v=>∑a,slot v a))).part s=
      ∑p:s.val → L,(connected (moments R f (put R s (fun v=>slot v.val (p v))))).part s:=by
  classical
  have pegs: (connected (moments R f (fun v=>∑a,slot v a))).part s=
      invoice R s f unit (fun v=>∑a,slot v.val a):=by
    apply equal_occurrences
    intro v hv
    simp [put,hv]
  rw [pegs,MultilinearMap.map_sum_finset,Fintype.piFinset_univ]
  rfl

end YM.Integration.WilsonOriginalCensusPageCumulant
end

