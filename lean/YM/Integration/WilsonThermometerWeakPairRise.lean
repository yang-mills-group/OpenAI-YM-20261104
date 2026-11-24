import YM.OPE.Orbits.Inclusions
import YM.OPE.Eye.Views

/-! Homogeneous basis letters keep their own engineering grade in the ordinary
measurement and in the independently read finite-probe coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairRise
open Finset Function Table Spec OPE OPE.Prescription OPE.Orbits
open scoped Classical BigOperators
variable {G:Gauge}{L:Register G}{S T:Table L}{Q:DiffPlan S}{I J:Type}[Fintype I][Fintype J]

def Move (Q:DiffPlan S)(a b:L.Token):Prop:=a=b ∨ ∃h:a.1≤b.1,Q.rise h (S.project _ a.2)=S.project _ b.2

private lemma replaceAll {X V:Type}(f:(I→V)→X)(p q:I→V)
    (change1:∀i r,f (update r i (p i))=f (update r i (q i))):f p=f q:=by
  let mix(s:Finset I)(i:I):=if i∈s then p i else q i
  have toggle (s:Finset I):f (mix s)=f q:=by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert i s notMem previous =>
      have fix (x:V) (v:I→V):update v i x i=x:=update_self i x v
      have left : mix (insert i s)=update (mix s) i (p i):=by
        funext j;by_cases h:j=i
        · subst j;simp [mix]
        · simp [mix,h]
      have right : mix s=update (mix s) i (q i):=by
        funext j;by_cases h:j=i
        · subst j;simp [mix,notMem]
        · simp [h]
      rw [left,change1,←right];exact previous
  simpa [mix] using toggle univ

lemma observation (sym:T.Symmetric)(res:T.respects S)(inc:Q.Inclusions T){x:I→E4}
    (room:Injective x){p q:I→L.Token}(rise:∀i,Move Q (p i) (q i)):
    observe T x p=observe T x q:=by
  apply replaceAll
  intro i v
  rcases rise i with h|⟨h,eq⟩
  · rw [h]
  · exact (observe_replace T v sym res inc room i h eq).symm
lemma coefficient (P:Prescription Q)(hp:P.Coherent)(sym:S.Symmetric)(inc:Q.Inclusions S)
    {p q:I→L.Token}(rise:∀i,Move Q (p i) (q i))(a:Mode Q)(x:I→E4)(o:E4):
    P.ope a x p o=P.ope a x q o:=by
  apply replaceAll (fun f=>P.ope a x f o)
  intro i v
  rcases rise i with h|⟨h,eq⟩
  · rw [h]
  · exact (Prescription.respectsLabel P v hp sym inc i h eq a).symm

lemma basis (P:Prescription Q){d:ℕ}(a:↥(bands Q d)):
    Move Q (P.letter a.1) ⟨d,S.representative d (P.loaded a.1 d)⟩:=by
  let h:= (full_bands ..).mp a.2
  right
  refine ⟨h,?_⟩
  change Q.rise h (S.project _ (S.representative _ (P.needle a.1)))=S.project _ (S.representative _ _)
  rw [S.rep,S.rep,Prescription.cost _ _ a.2]

theorem discrepancy (P:Prescription Q)(hp:P.Coherent)(s0:S.Symmetric)(i0:Q.Inclusions S)
    (st:T.Symmetric)(res:T.respects S)(inc:Q.Inclusions T){x:I→E4}{y:J→E4}{o:E4}
    (joined:Injective (beside x y))(emitted:Injective (beside (sole o) y))
    {p q:I→L.Token}{w v:J→L.Token}(np:∀j,Move Q (p j) (q j))(nf:∀j,Move Q (w j) (v j))(h:ℕ):
    observe T (beside x y) (beside p w) - P.truncated T h x p o y w =
      observe T (beside x y) (beside q v) - P.truncated T h x q o y v:=by
  refine congrArg₂ (fun a b:ℂ=>a-b) (observation st res inc joined (Sum.rec np nf)) ?_
  apply Finset.sum_congr rfl
  intro a _
  refine congrArg₂ (·*·) (coefficient P hp s0 i0 np a x o) (observation st res inc emitted ?_)
  exact Sum.rec (fun _=>Or.inl rfl) nf
end YM.Integration.WilsonThermometerWeakPairRise
end
