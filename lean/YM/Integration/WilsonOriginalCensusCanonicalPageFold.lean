import YM.Integration.WilsonReceivedDepositedOrbitalGrade

/-! Folding one independently chosen copy per occupied name commutes with the
ordinary-to-connected equation, including its empty face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalPageFold
open Function Finset WilsonCoeffUV.Wheel.Mark WilsonReceivedDepositedOrbitalGrade
open scoped Classical BigOperators
variable {I X U A:Type} [DecidableEq I] [Fintype U] [Zero X] [CommRing A]

def localOn (M:(I→X)→Sac I A):Prop:=
  ∀a b S,(∀j∈S,a j=b j)→M a S=M b S

def onFace (o:U→I→X)(S:Finset I)(p:S→U)(j:I):X:=
  if h:j∈S then o (p ⟨j,h⟩) j else 0

def folded (o:U→I→X)(M:(I→X)→Sac I A)(S:Finset I):A:=
  ∑p:S→U,M (onFace o S p) S

omit [Fintype U] [Zero X] in
theorem connected_local [IsAddTorsionFree A] {M L:(I→X)→Sac I A}
    (paid:∀a,Equation (M a) (L a))(hm:localOn M):localOn L:=by
  intro a b S same
  let e:S↪I:=Embedding.subtype _
  have order (t:Finset S):M a (t.map e)=M b (t.map e):=by
    apply hm
    intro j hj
    obtain ⟨i,_,rfl⟩:=mem_map.mp hj
    exact same i i.property
  have first:=restrict e (paid a)
  have second:=restrict e (paid b)
  rw [show (fun t:Finset S=>M a (t.map e))=(fun t:Finset S=>M b (t.map e)) from funext order] at first
  have equal:=congrFun (Equation.unique _ _ _ first second) S.attach
  simpa only [e,Finset.attach_map_val] using equal

/-- Restrict a page assignment to the two complementary faces of a cut. -/
def split {S T:Finset I}(sub:T⊆S):(S→U)≃((T→U)×(↥(S\T)→U)) where
  toFun p:=(fun j=>p ⟨j,sub j.property⟩,fun j=>p ⟨j,(mem_sdiff.mp j.property).1⟩)
  invFun z j:=if h:j.val∈T then z.1 ⟨j.val,h⟩ else z.2 ⟨j.val,mem_sdiff.mpr ⟨j.property,h⟩⟩
  left_inv p:=by
    funext j
    change (if h:j.val∈T then _ else _)=_
    split <;> rfl
  right_inv z:=by
    apply Prod.ext
    · funext j
      change (if h:j.val∈T then _ else _)=_
      rw [dif_pos j.property]
    · funext j
      change (if h:j.val∈T then _ else _)=_
      rw [dif_neg (mem_sdiff.mp j.property).2]

private theorem multiply (o:U→I→X) (F H:(I→X)→Sac I A) (lf:localOn F) (lh:localOn H)
    (S T:Finset I)(sub:T⊆S):
    (∑p:S→U,F (onFace o S p) T*H (onFace o S p) (S\T))=folded o F T*folded o H (S\T):=by
  let a (p:T→U):=F (onFace o T p) T
  let b (p:↥(S\T)→U):=H (onFace o (S\T) p) (S\T)
  calc
    _=∑p:S→U,a ((split sub) p).1*b ((split sub) p).2:=by
      apply sum_congr rfl
      intro p _
      apply congrArg₂ (·*·)
      · apply lf
        intro j hj
        simp only [onFace,dif_pos hj,dif_pos (sub hj)]
        rfl
      · apply lh
        intro j hj
        simp only [onFace,dif_pos hj,dif_pos (mem_sdiff.mp hj).1]
        rfl
    _=∑v:(T→U)×(↥(S\T)→U),a v.1*b v.2:=(split sub).sum_comp (fun v=>a v.1*b v.2)
    _=_:=by rw [Fintype.sum_prod_type];simp only [←Finset.mul_sum,←Finset.sum_mul,folded,a,b]

theorem original [IsAddTorsionFree A] (o:U→I→X){M L:(I→X)→Sac I A}
    (paid:∀a,Equation (M a) (L a))(localM:localOn M):Equation (folded o M) (folded o L):=by
  let localL:=connected_local paid localM
  refine ⟨?_,?_,?_⟩
  · simp [folded,(paid _).1]
  · simp [folded,(paid _).2.1]
  · funext S
    change S.card • (∑p:S→U,M (onFace o S p) S)=∑T∈S.powerset, (T.card • folded o L T)*folded o M (S\T)
    rw [Finset.smul_sum]
    have each (p:S→U):S.card • M (onFace o S p) S=
        ∑T∈S.powerset,(T.card • L (onFace o S p) T)*M (onFace o S p) (S\T):=
      congrFun (paid (onFace o S p)).2.2 S
    simp_rw [each]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun T hT=>?_
    simp_rw [smul_mul_assoc,←Finset.smul_sum]
    exact congrArg (T.card • ·) (multiply o L M localL localM S T (mem_powerset.mp hT))

end YM.Integration.WilsonOriginalCensusCanonicalPageFold
end
