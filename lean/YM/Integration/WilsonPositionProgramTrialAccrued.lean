import YM.Integration.WilsonPositionProgramTrialInverseJet
import YM.Integration.WilsonIndependentMatchedKernelResidual

/-! The measured coordinate of an entire K word carried on its own N vacuum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialAccrued
open Function Finset Matrix Lattice Wilson RG Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark
open WilsonPositionProgramTrialFittedLens (matrix ticket)
open WilsonPositionProgramTrialReverseLens (received)
open scoped BigOperators Classical
variable {G:Gauge}{k u e:ℕ}{H:Hol G}(Q:SealR G){w:Rails Q.h k u e}{E W B V:Credit}
variable (X:CutsP H Q.ans Q.path w E W B V)

def home:Q.Rider:=
  matrix (Wray X.ax X.tx Q.ans Q.path X.N X.m)
    (opal Q.F (spools X.ax X.tx X.N k Q.h X.m X.i X.pt))

theorem tally:home Q X=ticket X.ax X.tx Q X.N X.m X.ceilC X.tileP:=by
  have paid:=TallOracle X.L X.ha (X.hc.trans X.hn) X.pt X.sp
  change matrix _ (opal _ (spools _ _ _ _ _ _ _ _))=matrix _ (street _ _ _ _ _ _ (_-_) _)
  rw [show X.ceilC-X.m=X.i from Nat.add_sub_cancel_left X.m X.i]
  exact congrArg (matrix (Wray X.ax X.tx Q.ans Q.path X.N X.m)) paid

theorem returns:
    received X.ax X.tx Q X.m X.ceilC X.N (home Q X)=X.tileP ∧
    centralL X.ax X.tx X.N X.m X.ceilC Q (PermuteLens X.ax X.tx Q X.N X.m (home Q X))=
      Shrine X.Ntop X.tileP:=by
  have read:=WilsonPositionProgramTrialFittedLens.original H Q X.L.L X.ha
    (Nat.le_add_right X.m X.i) (X.hc.trans X.hn) X.tileP
  rw [tally Q X]
  exact ⟨read.2.1,read.2.2⟩

theorem source:
    X.pt=centralL X.ax X.tx X.N X.m X.ceilC Q
      (PermuteLens X.ax X.tx Q X.N X.m (home Q X))+X.springP X.i:=by
  rw [(returns Q X).2,X.carve1]
  abel

theorem issued (H:Hol G)(Q:SealR G)(w:Rails Q.h k u e)(E W B V:Credit):
    ∃C:Credit,∀X:CutsP H Q.ans Q.path w E W B V,
      X.tileP=opal Q.F X.pt+boot X.ax X.tx Q.ans Q.path X.N k X.ceilC X.m X.i
        (Silt X.Ntop X.pt) ∧
      received X.ax X.tx Q X.m X.ceilC X.N (home Q X)=X.tileP ∧
      X.pt=centralL X.ax X.tx X.N X.m X.ceilC Q
        (PermuteLens X.ax X.tx Q X.N X.m (home Q X))+X.springP X.i ∧
      (∀i<X.i,Spout X.ax X.tx X.N (X.m+i) Q.h k (X.springP (i+1))=X.springP i) ∧
      ∀t≤e,∀i≤X.i,∀r,Fruit 0 1 u ((X.springP i).2 t r)
        (C.buy X.Age*Real.exp (-(X.ax.S.scale X.ceilC-X.ax.S.scale (X.m+i))/4)*X.fuel):=by
  obtain ⟨C,paid⟩:=WilsonIndependentMatchedKernelResidual.original H Q.ans Q.path w E W B V
  refine ⟨C,fun X=>⟨?_,(returns Q X).1,source Q X,(paid X).2.1,(paid X).2.2⟩⟩
  change opal _ _+boot _ _ _ _ _ _ _ _ (X.ceilC-X.m) _=_
  rw [show X.ceilC-X.m=X.i from Nat.add_sub_cancel_left X.m X.i]

end YM.Integration.WilsonPositionProgramTrialAccrued
end
