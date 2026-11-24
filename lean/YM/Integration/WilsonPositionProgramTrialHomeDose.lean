import YM.Integration.WilsonPositionProgramTrialAccrued
import YM.Integration.WilsonIndependentFittedReportedWage
import YM.Integration.WilsonPositionProgramTrialFittedWick

/-! The normalized dose of the entire field on its original receiving date. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialHomeDose
open Function Finset Matrix Lattice Wilson RG Precision Source Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Mark
open WilsonPositionProgramTrialFittedLens (matrix ticket)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonOriginalPublicPlantedStableCredit (span)
open scoped BigOperators Classical
variable {G:Gauge}{k u e:ℕ}{H:Hol G}(Q:SealR G){w:Rails Q.h k u e}{E W B V:Credit}
variable (X:CutsP H Q.ans Q.path w E W B V)

def publicDose (a:ℝ):Q.Rider:=matrix (Wray X.ax X.tx Q.ans Q.path X.N X.m) (dose X a)

theorem filed (a:ℝ):publicDose Q X a=ticket X.ax X.tx Q X.N X.m X.ceilC (a • X.tileP):=by
  simp only [publicDose,ticket,dose,WilsonIndependentMatchedReportedProxy.reported,
    CutsP.ceilC,Nat.add_sub_cancel_left]

theorem original (a:ℝ):
    PermuteLens X.ax X.tx Q X.N X.m (publicDose Q X a)=dose X a ∧
    centralL X.ax X.tx X.N X.m X.ceilC Q (PermuteLens X.ax X.tx Q X.N X.m (publicDose Q X a))=
      a • Shrine X.Ntop X.tileP ∧
    a • X.pt=centralL X.ax X.tx X.N X.m X.ceilC Q
      (PermuteLens X.ax X.tx Q X.N X.m (publicDose Q X a))+a • X.springP X.i:=by
  have h:=WilsonPositionProgramTrialFittedLens.original H Q X.L.L X.ha
    (Nat.le_add_right X.m X.i) (X.hc.trans X.hn) (a • X.tileP)
  have read:PermuteLens X.ax X.tx Q X.N X.m (publicDose Q X a)=dose X a:=by
    rw [filed]
    simpa only [CutsP.ceilC,Nat.add_sub_cancel_left,dose,WilsonIndependentMatchedReportedProxy.reported] using h.1
  rw [read]
  refine ⟨rfl,WilsonIndependentMatchedFittedSeat.scaled X a,?_⟩
  rw [add_comm]
  exact (WilsonIndependentMatchedFittedSeat.taken X a).symm

theorem scaled (a:ℝ):publicDose Q X a=a • home Q X:=by
  have linear:street X.ax X.tx Q.ans Q.path X.N X.m X.i (a • X.tileP)=
      a • street X.ax X.tx Q.ans Q.path X.N X.m X.i X.tileP:=by
    unfold street
    rw [←Matrix.mulVec_smul]
    congr 1
    funext i
    exact map_smul (PowerSeries.substAlgHom _) a _
  rw [WilsonPositionProgramTrialAccrued.tally Q X]
  simp only [publicDose,ticket,CutsP.ceilC,Nat.add_sub_cancel_left,dose,
    WilsonIndependentMatchedReportedProxy.reported,linear]
  funext i
  simp only [matrix,Pi.smul_apply,Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _=>smul_comm _ _ _

theorem wage (H:Hol G)(Q:SealR G)(w:Rails Q.h k u e)(E W B V:Credit):
    ∃C:Credit,∀(X:CutsP H Q.ans Q.path w E W B V)(a b:ℝ),
      (∀i j,‖Wray X.ax X.tx Q.ans Q.path X.N X.m i j‖≤b) →
      ∀t≤e,∀i,‖coeff t (publicDose Q X a i)‖≤
        Fintype.card (Alma Q.F)*b*((Real.exp (span X X.i))^Q.h*C.buy X.Age*(|a| * X.fuel)):=by
  obtain ⟨C,priced⟩:=WilsonIndependentFittedReportedWage.original H Q.ans Q.path w E W B V
  refine ⟨C,?_⟩
  intro X a b shop t ht i
  let cap:=(Real.exp (span X X.i))^Q.h*C.buy X.Age*(|a| * X.fuel)
  calc
    ‖coeff t (publicDose Q X a i)‖ ≤ ∑j:Alma Q.F,
        ‖Wray X.ax X.tx Q.ans Q.path X.N X.m i j‖*‖coeff t (dose X a j)‖:=by
      simp only [publicDose,matrix,map_sum,map_smul]
      exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_smul]))
    _ ≤ ∑_j:Alma Q.F,b*cap:=by
      apply sum_le_sum
      intro j _
      exact mul_le_mul (shop i j) (priced X a t ht j) (norm_nonneg _) ((norm_nonneg _).trans (shop i j))
    _ = _:=by simp only [sum_const,card_univ,nsmul_eq_mul,cap];ring

end YM.Integration.WilsonPositionProgramTrialHomeDose
end
