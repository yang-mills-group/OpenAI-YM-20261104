import YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeRawFaces
/-! A genuine physical leaf occurs exactly once in each original complete
casting. The other parent factors and all intermediate labels keep their
original values on this same file. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeLeafSlot
open Function OPE OPE.Orbits OPE.Arboreal Table
open scoped Classical BigOperators
open WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeRawFaces (entered grades)
variable {G:Gauge}{L:Register G}{S:Table L}{H:DiffPlan S}(P:Prescription H)
  {I:Type}[Fintype I][DecidableEq I](tree:Arboreal I)(d:I→ℕ)
def shift {a b:ℕ}(eq:a=b):S.Field a→ₗ[ℂ]S.Field b:=eq ▸ LinearMap.id
private theorem shift_apply {a b:ℕ}(eq:a=b)(v:S.Field a):
    shift (S:=S) eq v=cast (congrArg S.Field eq) v:=by
  subst b
  rfl
omit [DecidableEq I] in
private theorem outside (l:tree.leaves):l.val∉tree.zones:=
  ((tree.live_iff tree.zones l.val).mp l.property).1
def key (l:tree.leaves):tree.kids (tree.parent l.val):=by
  refine ⟨l.val,(tree.related ..).mpr ⟨?_,rfl⟩⟩
  intro eq
  have active:tree.root∈tree.zones:=by simpa only [tree.direct] using tree.inward tree.root
  exact outside tree l (by simpa only [eq] using active)
theorem old (hS:S.Hierarchy)(x:I→E4)(w:Labels S d)(f:I→Mode H)(l:tree.leaves)
    (i:I)(other:i≠tree.parent l.val)(u:S.Field (d l.val)):
    eventAt P tree tree.zones x (names (Function.update w l.val u)) i f=
      eventAt P tree tree.zones x (names w) i f:=by
  rw [WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeRawFaces.parent P tree d hS,
    WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeRawFaces.parent P tree d hS]
  congr 1
  funext j
  have distinct:j.val≠l.val:=by
    intro e
    exact other (((tree.related ..).mp j.property).2.symm.trans (congrArg tree.parent e))
  by_cases charged:j.val∈tree.zones <;> simp [entered,charged,Function.update_of_ne distinct]
theorem localBill (hS:S.Hierarchy)(x:I→E4)(w:Labels S d)(f:I→Mode H)(l:tree.leaves):
    ∃ L:S.Field (d l.val)→ₗ[ℂ]ℂ,∀u,
       eventAt P tree tree.zones x (names (Function.update w l.val u)) (tree.parent l.val) f=L u:=by
  let seat:=key tree l
  let row:=checkRow (d:=fun j:tree.kids (tree.parent l.val)=>grades d tree.zones f j.val)
        P (f (tree.parent l.val)) (crop x (tree.kids (tree.parent l.val))) (x (tree.parent l.val))
  let before:=fun j:tree.kids (tree.parent l.val)=>entered P d tree.zones f w j.val
  have home:d l.val=grades d tree.zones f seat.val:=by simp [seat,key,grades,outside tree l]
  refine ⟨(row.toLinearMap before seat).comp (shift (S:=S) home),fun u=>?_⟩
  rw [WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeRawFaces.parent P tree d hS]
  change row _=row (Function.update before seat (shift (S:=S) home u))
  congr 1
  funext j
  by_cases eq:j=seat
  · subst j
    rw [Function.update_self]
    simp [seat,key,entered,grades,outside tree l]
    exact (shift_apply (S:=S) home u).symm
  rw [Function.update_of_ne eq]
  have diff:j.val≠l.val:=fun hit=>eq (Subtype.ext hit)
  by_cases borne:j.val∈tree.zones <;> simp [before,entered,borne,Function.update_of_ne diff]
theorem original (hS:S.Hierarchy)(x:I→E4)(w:Labels S d)(f:I→Mode H)(l:tree.leaves):
    ∃ L:S.Field (d l.val)→ₗ[ℂ]ℂ,∀u,
      ensemble P tree tree.zones x (names (Function.update w l.val u)) f=L u:=by
  classical
  obtain ⟨paid,funded⟩:=localBill P tree d hS x w f l
  let prior:=∏i∈tree.zones.erase (tree.parent l.val),eventAt P tree tree.zones x (names w) i f
  refine ⟨prior•paid,fun u=>?_⟩
  unfold ensemble
  rw [←Finset.mul_prod_erase tree.zones _ (tree.inward l.val),funded u]
  have same:(∏i∈tree.zones.erase (tree.parent l.val),
        eventAt P tree tree.zones x (names (Function.update w l.val u)) i f)=prior:=by
    apply Finset.prod_congr rfl
    intro i hi
    exact old P tree d hS x w f l i (Finset.mem_erase.mp hi).1 u
  rw [same]
  exact mul_comm _ _
end YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeLeafSlot
end
