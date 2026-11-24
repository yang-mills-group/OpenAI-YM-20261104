import YM.Integration.WilsonOriginalAlternativeFiniteSource
import YM.Integration.WilsonOriginalAlternativeNames
import YM.QuadraticLocal.Germ.Stock

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeRetest
open Function Finset Set Marker QuadraticLocal QuadraticLocal.Affinity
open WilsonOriginalAlternativeNames
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] {X:V→Type} [∀i,AddCommGroup (X i)] [∀i,Module ℝ (X i)]
  (A:∀i,Set (X i)) (K:∀i,Submodule ℝ (X i)) (zero:∀i,0∈A i) (c:V→Port)

/-- Old data are evaluated at their original incoming test in the physical and
signed slots. A guarded-only slot contributes zero to all its old incidences. -/
def submitted (x:Wallet A):Wallet A:=fun i=>if c i=1 then ⟨0,zero i⟩ else x i

variable {Y:Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {s:Finset V} {F:Wallet A→Y}

theorem evaluated (earn:Attn K A s F) (x:Wallet A):
    F (submitted A zero c x)=if ∀v∈s,c v≠1 then F x else 0:=by
  split_ifs with live
  · exact earn.sit _ _ (fun i hi=>if_neg (live i hi))
  · obtain ⟨j,hj,one⟩:∃j∈s,c j=1:=by simpa using live
    exact earn.idle j hj _ (by simp [submitted,one])

theorem attentive (earn:Attn K A s F):Attn K A s (fun x=>F (submitted A zero c x)):=by
  simp_rw [evaluated A K zero c earn]
  by_cases live:∀v∈s,c v≠1
  · simpa only [if_pos live] using earn
  · simp only [if_neg live]
    exact Attn.silent

theorem ink (J:Census V) (s:J.Mode):∏v∈s.val,retain (c v)=if ∀v∈s.val,c v≠1 then 1 else 0:=by
  split_ifs with live
  · exact Finset.prod_eq_one fun v hv=>if_neg (live v hv)
  · obtain ⟨j,hj,one⟩:∃j∈s.val,c j=1:=by simpa using live
    exact Finset.prod_eq_zero hj (if_pos one)

theorem printed {J:Census V} (s:J.Mode) {g:Wallet A→ℂ} (earn:Attn K A s.val g) (x:Wallet A):
    g (submitted A zero c x)=(∏v∈s.val,retain (c v))*g x:=by
  rw [evaluated A K zero c earn,ink c J]
  split_ifs <;> simp

end YM.Integration.WilsonOriginalAlternativeRetest
