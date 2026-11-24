import YM.Integration.WilsonIndependentConditionedFolioStations
import YM.Integration.WilsonIndependentConditionedFolioFiled

/-! The actual socket deposits and complete reported K payment on the two-name
catalogue, including its zero slot. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedLocatedPairPayment
open Function Finset Lattice Wilson RG Source Labels
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open Extra.Histories WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonIndependentConditionedPlacementArm (head)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonOriginalPublicNodalTestedFunctional (deposit visits)
open WilsonReceivedCanonicalSocketSeed (contact sheet present)
open WilsonOlderFreshSoftSocketMeasuredCash (seats)
open WilsonIndependentConditionedFolioWeights (payment)
open WilsonPositionProgramReportedField (entire)
open WilsonIndependentConditionedFolioTerm (picks)
open scoped Classical BigOperators ContDiff
abbrev J:=Fin 2

theorem deposit_one {I:Type}[Fintype I][DecidableEq I](D:I→ℕ)(pt:I→Chamber)(S:Finset I):
    touch (present D) S (deposit D (fun i=>contact (D i)) pt S)=1:=by
  rw [WilsonOriginalPublicNodalTestedFunctional.visits]
  apply Finset.prod_eq_one
  intro i _
  change crease (sheet (D i.val)) Fin.elim0 (pt i.val).val=1
  simp [crease,sheet,iteratedFDeriv_zero_apply]

def pairEquiv (A:J→Type*):((i:(univ:Finset J))→A i.val) ≃ A 0×A 1 where
  toFun c:=(c ⟨0,mem_univ _⟩,c ⟨1,mem_univ _⟩)
  invFun p s:=Fin.cons p.1 (Fin.cons p.2 (fun j=>j.elim0)) s.val
  left_inv f:=by funext s;rcases s with ⟨s,h⟩;fin_cases s <;> rfl
  right_inv p:=rfl

theorem sum {A:J→Type*}[∀i,Fintype (A i)]{X:Type*}[AddCommMonoid X]
    (f:((i:(univ:Finset J))→A i.val)→X):
    ∑b,f b=∑u,∑v,f ((pairEquiv A).symm (u,v)):=by
  calc
    _ = ∑p:A 0 × A 1,f ((pairEquiv A).symm p):=Fintype.sum_equiv (pairEquiv A) _ _ (fun _=>by simp)
    _ = _:=Fintype.sum_prod_type _

variable {G:Gauge}(R:Run G)(d:J→ℕ)(K N per:ℕ)
local notation "F" => R.family.labels.level
def ballot (station:J→ℕ)(axes:∀i,R.family.label (d i) ≃ₗ[ℂ] R.family.label (d i))
    (Y:∀i,R.family.label (d i))(turn:J→Signed)(hand:J→Bool)(phase:J→ℂ)(i:J):R.family.label (d i):=
  (phase i*(((R.family.S.a K:ℂ)^(d i))⁻¹)) •
    Motion.patch (F (d i)) (turn i,hand i) ((axes i).symm (fitted R (d i) (station i) N per (Y i)))

theorem actual (station:J→ℕ)(axes:∀i,R.family.label (d i) ≃ₗ[ℂ] R.family.label (d i))
    (Y:∀i,R.family.label (d i))(turn:J→Signed)(hand:J→Bool)(phase:J→ℂ)(i:J):
    entire R (d i) K (N,per) (ballot R d K N per station axes Y turn hand phase i)=
      head R (d i) (station i) K N per (axes i) (Y i) (turn i) (hand i) (phase i):=rfl

theorem both (w:∀i,R.family.label (d i))(u:(F (d 0)).Index)(v:(F (d 1)).Index):
    payment R d N per K w univ ((pairEquiv (fun i=>(F (d i)).Index)).symm (u,v))=
      entire R (d 0) K (N,per) (w 0) u*entire R (d 1) K (N,per) (w 1) v:=by
  let e:(univ:Finset J) ≃ J:=⟨Subtype.val,fun i=>⟨i,mem_univ _⟩,fun _=>rfl,fun _=>rfl⟩
  rw [payment]
  calc
    _ = ∏i:J,entire R (d i) K (N,per) (w i) (picks R d u v i):=Fintype.prod_equiv e _ _ (fun _=>rfl)
    _ = _:=by rw [Fin.prod_univ_two];rfl
end YM.Integration.WilsonIndependentConditionedLocatedPairPayment
end
