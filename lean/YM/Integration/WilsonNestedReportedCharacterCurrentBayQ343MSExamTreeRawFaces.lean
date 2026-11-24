import YM.Integration.WilsonOrdinaryNestedCourse
/-! Every actually retained parent in the unaveraged geometric tree is the
multilinear registered sheet at the correct grades, including every earlier
intermediate needle and the unchanged old physical inputs at the other seats. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeRawFaces
open Function OPE OPE.Orbits OPE.Arboreal Table
open scoped Classical BigOperators
variable {G:Gauge}{L:Register G}{S:Table L}{H:DiffPlan S}(P:Prescription H)
  {I:Type}[Fintype I](tree:Arboreal I)(d:I→ℕ)
def grades (a:Finset I)(f:I→Mode H)(i:I):ℕ:=if i∈a then (f i).1 else d i
def entered (a:Finset I)(f:I→Mode H)(w:Labels S d)(i:I):S.Field (grades d a f i):=
  if hi:i∈a then cast (congrArg S.Field (show (f i).1=grades d a f i by simp [grades,hi])) (P.needle (f i))
  else cast (congrArg S.Field (show d i=grades d a f i by simp [grades,hi])) (w i)
private theorem passage {a b:ℕ}(he:a=b)(v:S.Field a):
    (⟨b,S.representative b (cast (congrArg S.Field he) v)⟩:L.Token)=⟨a,S.representative a v⟩:=by
  subst b
  rfl
omit [Fintype I] in
theorem named (a:Finset I)(f:I→Mode H)(w:Labels S d):
    names (entered P d a f w)=audition P a (names w) f:=by
  funext i
  by_cases hi:i∈a
  · unfold names entered audition
    rw [dif_pos hi,if_pos hi]
    exact passage (S:=S) (a:=(f i).1) (b:=grades d a f i) (by simp [grades,hi]) (P.needle (f i))
  unfold names entered audition
  rw [dif_neg hi,if_neg hi]
  exact passage (S:=S) (a:=d i) (b:=grades d a f i) (by simp [grades,hi]) (w i)
theorem root (hS:S.Hierarchy)(x:I→E4)(w:Labels S d)(ξ:Mode H):
    coalesce P tree.leaves x (names w) tree.root ξ=
      checkRow P ξ (crop x tree.leaves) (x tree.root)
        (fun i:tree.leaves=>w i.val):=by
  rw [check_eq P ξ hS]
  rfl
theorem parent (hS:S.Hierarchy)(a:Finset I)(x:I→E4)(w:Labels S d)(f:I→Mode H)(i:I):
    eventAt P tree a x (names w) i f=
      checkRow P (f i) (crop x (tree.kids i)) (x i)
        (fun j:tree.kids i=>entered P d a f w j.val):=by
  unfold eventAt coalesce
  rw [check_eq P (f i) hS,←named P d a f w]
  rfl
theorem original (hS:S.Hierarchy)(x:I→E4)(w:Labels S d)(ξ:Mode H)(D:I→ℕ):
    coalesce P tree.leaves x (names w) tree.root ξ-Arboreal.factorization P tree tree.zones x (names w) ξ D=
      checkRow P ξ (crop x tree.leaves) (x tree.root) (fun i:tree.leaves=>w i.val)-
      ∑f∈tree.casting tree.zones D ξ,∏i∈tree.zones,
        checkRow P (f i) (crop x (tree.kids i)) (x i)
          (fun j:tree.kids i=>entered P d tree.zones f w j.val):=by
  rw [root P tree d hS]
  unfold Arboreal.factorization ensemble
  simp_rw [parent P tree d hS]
end YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeRawFaces
end
