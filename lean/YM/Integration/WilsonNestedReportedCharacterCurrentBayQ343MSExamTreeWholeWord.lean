import YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeLeafSlot
import YM.OPE.Nesting.Kernels
/-! The unaveraged signed whole-tree difference on the genuine raw file is
multilinear in exactly its leaves. All intermediate needles, casts, and
unchanged factors keep their original filed values at the very same positions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeWholeWord
open Function OPE OPE.Orbits OPE.Arboreal Table
open scoped Classical BigOperators
variable {G:Gauge}{L:Register G}{S:Table L}{H:DiffPlan S}(P:Prescription H)
  {I:Type}[Fintype I][DecidableEq I](tree:Arboreal I)(d:I→ℕ)
def filled (w:Labels S d)(v:Labels S (fun i:tree.leaves=>d i.val)):Labels S d:=fun i=>
  if hi:i∈tree.leaves then v ⟨i,hi⟩ else w i
theorem updated [DecidableEq ↥tree.leaves] (w:Labels S d)(v:Labels S (fun i:tree.leaves=>d i.val))(l:tree.leaves)
    (u:S.Field (d l.val)):
    filled tree d w (Function.update v l u)=Function.update (filled tree d w v) l.val u:=by
  funext i
  by_cases e:i=l.val
  · subst i
    simp [filled,l.property]
  rw [Function.update_of_ne e]
  by_cases live:i∈tree.leaves
  · have other:(⟨i,live⟩:tree.leaves)≠l:=fun he=>e (congrArg Subtype.val he)
    simp [filled,live,Function.update_of_ne other]
  simp [filled,live]
theorem agree (x:I→E4)(v u:Labels S d)(ξ:Mode H)(D:I→ℕ)(same:∀i:tree.leaves,v i.val=u i.val):
    coalesce P tree.leaves x (names v) tree.root ξ-factorization P tree tree.zones x (names v) ξ D=
    coalesce P tree.leaves x (names u) tree.root ξ-factorization P tree tree.zones x (names u) ξ D:=by
  have top:crop (names v) tree.leaves=crop (names u) tree.leaves:=by
    funext i
    exact congrArg (fun z:S.Field (d i.val)=>Sigma.mk (d i.val) (S.representative _ z)) (same i)
  have lower (f:I→Mode H):audition P tree.zones (names v) f=audition P tree.zones (names u) f:=by
    funext i
    by_cases hi:i∈tree.zones
    · simp [audition,hi]
    have leaf:i∈tree.leaves:=(tree.live_iff tree.zones i).mpr ⟨hi,tree.inward i⟩
    simp [audition,hi,names,same ⟨i,leaf⟩]
  unfold Arboreal.factorization ensemble eventAt coalesce
  simp_rw [lower,top]
theorem seated [DecidableEq ↥tree.leaves] (hS:S.Hierarchy)(x:I→E4)(w:Labels S d)(f:I→Mode H)
    (v:Labels S (fun i:tree.leaves=>d i.val))(i:tree.leaves):
    ∃A:S.Field (d i.val)→ₗ[ℂ]ℂ,∀u,
      ensemble P tree tree.zones x (names (filled tree d w (Function.update v i u))) f=A u:=by
  obtain ⟨paid,actual⟩:=WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeLeafSlot.original
    P tree d hS x (filled tree d w v) f i
  refine ⟨paid,fun u=>?_⟩
  rw [updated tree d w v i u]
  exact actual u

def single (hS:S.Hierarchy)(x:I→E4)(w:Labels S d)(f:I→Mode H):
    MultilinearMap ℂ (fun i:tree.leaves=>S.Field (d i.val)) ℂ where
  toFun v:=ensemble P tree tree.zones x (names (filled tree d w v)) f
  map_update_add' v i a b:=by
    obtain ⟨paid,actual⟩:=seated P tree d hS x w f v i
    change ensemble P tree tree.zones x (names (filled tree d w (Function.update v i (a+b)))) f=
      ensemble P tree tree.zones x (names (filled tree d w (Function.update v i a))) f+
      ensemble P tree tree.zones x (names (filled tree d w (Function.update v i b))) f
    rw [actual (a+b),actual a,actual b,map_add]
  map_update_smul' v i c a:=by
    obtain ⟨paid,actual⟩:=seated P tree d hS x w f v i
    change ensemble P tree tree.zones x (names (filled tree d w (Function.update v i (c•a)))) f=
      c•ensemble P tree tree.zones x (names (filled tree d w (Function.update v i a))) f
    rw [actual (c•a),actual a,map_smul]
def word (hS:S.Hierarchy)(x:I→E4)(w:Labels S d)(ξ:Mode H)(D:I→ℕ):
    MultilinearMap ℂ (fun i:tree.leaves=>S.Field (d i.val)) ℂ:=
  checkRow P ξ (crop x tree.leaves) (x tree.root)-
    ∑f∈tree.casting tree.zones D ξ,single P tree d hS x w f
theorem original (hS:S.Hierarchy)(x:I→E4)(w:Labels S d)(ξ:Mode H)(D:I→ℕ)(v:Labels S d):
    word P tree d hS x w ξ D (fun i=>v i.val)=
    coalesce P tree.leaves x (names v) tree.root ξ-factorization P tree tree.zones x (names v) ξ D:=by
  let b:=filled tree d w (fun i:tree.leaves=>v i.val)
  have live(i:tree.leaves):b i.val=v i.val:=by simp [b,filled,i.property]
  rw [←agree P tree d x b v ξ D live]
  rw [WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeRawFaces.root P tree d hS]
  have tuple:(fun i:tree.leaves=>b i.val)=(fun i:tree.leaves=>v i.val):=funext live
  rw [tuple]
  unfold word Arboreal.factorization
  simp only [_root_.sub_apply,_root_.sum_apply]
  rfl
end YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeWholeWord
end
