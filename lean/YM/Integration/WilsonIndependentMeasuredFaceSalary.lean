import YM.Integration.WilsonIndependentRawPhysicalFaces
import YM.Integration.WilsonPhysicalOrientedPivotSalary

/-! Total variation of the actual fitted coefficients in the measured figure
after applying its genuine original directional and incoming prices. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMeasuredFaceSalary
open Lattice RG Source Labels XSpace PhysicalNext.Repeat.Legato
open WilsonIndependentRawPhysicalFaces (weight)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonPhysicalOrientedStencilPin (coordinates dosesAt)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntrancePanel (Panel)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n → ℕ)(S:Finset (Fin n))
local notation "δ" => (fun i:S=>d i)
theorem variation (v:(i:Fin n) → (R.family.labels.level (d i)).Coeff):
    ∑a:Columns R δ,‖weight R d v S a‖=∏i:S,(R.family.labels.level (d i)).coeffSize (v i):=by
  simp only [weight,norm_prod,Labels.Frame.coeffSize]
  exact (Fintype.prod_sum (fun i:S=>(fun j:(R.family.labels.level (d i)).Index=>‖v i j‖))).symm

variable {N per K f requested power age:ℕ}{B:ℝ}(file:Filed R d K){fk:f≤K}{kn:K≤N}
  (A:Panel R d N per f K fk kn requested power age B)
  (station:A.slot=file.station)(axes:A.axis=file.A N per)
local notation "heat" => R.family.path.levels.clock.hatBeta K
include station axes in
theorem original:
    ∑a:Columns R δ,‖weight R d (coordinates R d (N:=N) (per:=per) file A.names A.turn) S a‖ ≤
      ∏i:S,(2:ℝ)^(Finset.univ.sup (fun j:(R.family.labels.level (d i)).Index=>Prod.snd ((R.family.labels.level (d i)).grades j)))*(B*heat^power):=by
  rw [variation]
  apply Finset.prod_le_prod
  · intro i _
    exact Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  · intro i _
    exact (WilsonPositionProgramReportedField.purchased R (d i) K (N,per) kn
      (dosesAt R d (N:=N) (per:=per) file A.names A.turn i)).trans
      (mul_le_mul_of_nonneg_left (WilsonPhysicalOrientedPivotSalary.original R d file A station axes i)
        (by positivity))

end YM.Integration.WilsonIndependentMeasuredFaceSalary
