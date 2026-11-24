import YM.Integration.WilsonPositionProgramBlockedTrialNodes
import YM.Integration.WilsonPositionProgramSubmittedCoordinates
import YM.Integration.WilsonPositionProgramReportedField
/-! The trial's independently enrolled numerical labels at its actual blocked
birthday. Rank powers are charged once at that date, on each genuine root. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonPositionProgramBlockedTrialFiling
open Finset Lattice RG Wilson Labels Source Extra.Multi
open PhysicalNext.Repeat.Legato RG16 RG16.Literal Pert.Asymptotics Trace.Physical.GermGraph Extra.Histories
open WilsonPositionProgramBlockedTrialAddBack WilsonPositionProgramReportedField
open WilsonPositionProgramSubmittedCoordinates WilsonMarkedIndependentNormalizedElection
open WilsonCoeffUV WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d

def atomAt (N p K:ℕ) (o:Site ((C₀).side K p)) (i:(F₀).Index)(U:Config G ((C₀).side K p)):ℂ:=
  let g:=regulatorRun C₀ N p K
  (g^((F₀).grades i).2:ℝ)⁻¹ • (S₀).places (Pi.single i 1) o U

theorem filed (N p K:ℕ)(live:K≤N)(o:Site ((C₀).side K p))(v:(C₀).label d)(U:Config G ((C₀).side K p)):
    uncut R d N p K o v U=∑i,entire R d K (N,p) v i * atomAt R d N p K o i U:=by
  let g:=regulatorRun C₀ N p K
  let θ:=((C₀).path.rep N p K).p.threshold
  have gp : g≠0:=(ActualRunKernelPackets.regulator_pos R N p K live).ne'
  have θp:θ≠0:=((C₀).path.rep N p K).p.threshold_pos.ne'
  have basis0:(S₀).places (Pi.single 0 1) o U=1:=congrFun (R.makes.sections d).unit (expandAt o U)
  have split (i:(F₀).Index) :
      entire R d K (N,p) v i * atomAt R d N p K o i U =
        (if i=0 then v 0 else 0) + names R d N p K v i * (S₀).places (Pi.single i 1) o U:=by
    by_cases z:i=0
    · subst i;simp [WilsonPositionProgramReportedField.entire,atomAt,names,gMap,Frame.scaled_apply,Frame.zero_degree,Frame.core,basis0]
    · simp only [if_neg z,zero_add]
      let k:=((F₀).grades i).2
      have h:(g/θ)^k*(g^k)⁻¹=(θ⁻¹)^k:=by rw [div_pow,inv_pow];field_simp
      change ((F₀).scaled (g/θ) v i) * ((g^k)⁻¹ • (S₀).places (Pi.single i 1) o U) =
        (F₀).scaled θ⁻¹ ((F₀).core v) i * (S₀).places (Pi.single i 1) o U
      rw [Frame.scaled_apply,Frame.scaled_apply,Complex.real_smul]
      simp only [Frame.core,LinearMap.coe_mk,AddHom.coe_mk,Function.update_of_ne z]
      have hh:(((g/θ)^k:ℝ):ℂ)*(((g^k)⁻¹:ℝ):ℂ)=(((θ⁻¹)^k:ℝ):ℂ):=by exact_mod_cast h
      calc _ = ((((g/θ)^k:ℝ):ℂ)*(((g^k)⁻¹:ℝ):ℂ))*v i*(S₀).places (Pi.single i 1) o U:=by dsimp only [k];ring
           _ = _ :=by rw [hh]
  simp_rw [split]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',mem_univ,if_true]
  unfold uncut
  have cols:=congrFun (BasisCost.placed_columns S₀ (names R d N p K v) o) U
  exact congrArg (v 0+·) (by simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using cols)

theorem price (N p K:ℕ)(live:K≤N)(v:(C₀).label d):
    (F₀).coeffSize (entire R d K (N,p) v)≤2^(Finset.univ.sup (fun i:(F₀).Index=>((F₀).grades i).2))*(F₀).coeffSize v:=
  WilsonMasterCoordinatePrice.positive_grade R.makes N p d K live v

end YM.Integration.WilsonPositionProgramBlockedTrialFiling
end
