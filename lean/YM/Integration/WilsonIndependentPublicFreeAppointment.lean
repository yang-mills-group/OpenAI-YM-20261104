import YM.Integration.WilsonIndependentPublicFreeFields
import YM.Integration.WilsonIndependentCutJoinGrant

/-! Read each selected finite Wick spring on the circuit with the original public inversion prices. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPublicFreeAppointment
open Lattice RG XSpace Precision Source WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open WilsonCoeffUV
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open WilsonIndependentExactPlate
open WilsonIndependentEvenPassport (old)
open scoped Classical BigOperators
open WilsonIndependentCutJoinPassport (All)

variable {G:Gauge}{H:Hol G}(R:Master H)(chart:ChartRatio G)(K:KernelChoices)
    (V:XSpace.Run)(e h k j extra:ℕ)(B:WilsonIndependentEvenPassport.Menu R chart K V e h k j extra)
theorem original (grant:WilsonIndependentCutJoinPlate.Approved R chart K V e h k j extra B) (hj:4≤j)
    (i:Requests B.a)(Y:Program K)(Z:∀ P:Patch,P.Branches K G):
    let C:=S V B.a B.positive j hj
    let n:=M V B.a i
    let r:Fin B.a:=⟨i.val%B.a,Nat.mod_lt _ B.positive⟩
    ∃ (A:Levels G)(s:ℕ),All R A chart (extendedY (B.price r) A.S (s+n)) e s h k ∧
      A.S.scale (s+n)-A.S.scale (s+old V B.a i.val)= -Real.log (V.step i.val).spacing ∧
      (∀ p:Page (M V B.a),p.bindW=i→(C.tables Y p).diagonal=freeForms A (s+n) (s+(n-p.downW))) ∧
      ∀ f:Flap (M V B.a),f.volW=i→∀ c:Side,WilsonIndependentPublicFreeFields.Reads A C K s i Y Z f c :=by
  intro C n r
  obtain ⟨A,s,kin,grades,patch,gap,_,fund⟩:=WilsonIndependentCutJoinPlate.optics R chart K V e h k j extra B grant hj i
  have book:WilsonIndependentPublicFreeTrain.Matches A C K s i:=⟨kin,grades,fun f hf=>patch f hf 0⟩
  exact ⟨A,s,fund,gap,WilsonIndependentPublicFreeTrain.diagonal book Y,WilsonIndependentPublicFreeFields.original book Y Z⟩

end YM.Integration.WilsonIndependentPublicFreeAppointment
