import YM.Integration.WilsonMeasuredPublicEntranceRecordedWick
import YM.Integration.WilsonPhysicalStationThermalRanks

/-! Wick-rank orthogonality for the submitted Wilson coordinates and the actual
reflected probe, including raw coordinates that vanish in the free quotient. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceThermalRankPair
open Lattice Wilson RG Source Cells Extraction Table Extra.FD Maxwell Maxwell.Wick
open scoped Classical BigOperators
variable {G:Gauge}(C:Family G){d:ℕ}
local notation "F" => C.labels.level d
local notation "T" => standard C

theorem axis (a:(F).Index):Length (writes C.labels d ((T).project d (Pi.single a 1))) ((F).grades a).2:=by
  have eq:pack C.labels a=(T).project d (Pi.single a 1):=by
    change (T).project d ((F).coords ((F).basis a))=_
    rw [(F).coords_basis]
    rfl
  rw [←eq]
  intro k hk
  exact congrArg Prod.snd ((weight_collapse k).symm.trans (at_alcove C.labels d a hk))

theorem submitted (y:C.label d)(q:ℕ)(count:WilsonPhysicalThermalWickRankSupport.Counted F y q):
    Length (writes C.labels d ((T).project d y)) q:=by
  let basis:=Pi.basisFun ℂ (F).Index
  have pay:y=∑i:(F).Index,y i • Pi.single i (1:ℂ):=by
    simpa only [basis,Pi.basisFun_repr,Pi.basisFun_apply] using (basis.sum_repr y).symm
  let L:((F).Index→ℂ)→ₗ[ℂ] WickPol G:=(writes C.labels d).comp ((T).project d)
  change Length (L y) q
  rw [pay,_root_.map_sum L]
  change _ ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ letterCount q
  apply Submodule.sum_mem
  intro i _
  rw [L.map_smul]
  by_cases off:y i=0
  · rw [off,zero_smul]
    exact Submodule.zero_mem _
  apply Submodule.smul_mem
  rw [←WilsonPhysicalThermalWickRankSupport.support F y q count i off]
  exact axis C i

theorem original (a b:(F).Index)(s:Signed)(e:Fin 2)(x:Points 2)
    (off:((F).grades a).2≠((F).grades b).2):
    (T).classMoment T (fun _:Fin 2=>d) x ![(T).project d (Pi.single a 1),
      WilsonPhysicalStationThermalRanks.probe C b s e]=0:=by
  let v:=WilsonPhysicalStationThermalRanks.probe C b s e
  let h:Fin 2→(T).Field d:=![(T).project d (Pi.single a 1),v]
  have right:Length (writes C.labels d v) ((F).grades b).2:=by
    have seen:=submitted C (Further.CorrectedLift.ladder C d v) _ (WilsonPhysicalThermalWickProbe.original C b s e)
    rwa [Further.CorrectedLift.ladder_reads] at seen
  change (T).useAt T x (fun i=>⟨d,h i⟩)=0
  rw [writes_eval]
  change moment G x (fun i=>writes C.labels d (h i))=0
  rw [show (fun i=>writes C.labels d (h i))=![writes C.labels d ((T).project d (Pi.single a 1)),
    writes C.labels d v] from funext (fun i=>by fin_cases i <;> rfl)]
  exact FVAAlt2.Home.Report.stepNone _ _ x (axis C a) right off
end YM.Integration.WilsonMeasuredPublicEntranceThermalRankPair

