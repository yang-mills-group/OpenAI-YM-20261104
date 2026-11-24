import YM.Integration.WilsonOriginalTwoFlatChronology
import YM.Integration.WilsonOriginalJointTrialHearing

/-! The ordinary defect of a complete joint filing on the original earlier Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalReadout
open Function Finset MeasureTheory Lattice RG Wilson Marker
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(N per:ℕ){V:Type}[DecidableEq V]{J:Census V}
local notation "H" => R.family.path
local notation "X" j:max => Config G (R.family.side j per)

def face (rows:∀j,X j → Poly J)(s:J.Mode)(j:ℕ)(U:X j):ℂ:=
  (((H).rep N per j).eval U:ℂ)⁻¹*(rows j U).part s

theorem density (rows:∀j,X j → Poly J)(s:J.Mode){j:ℕ}(live:j≤N):
    numerator R N per j (face R N per rows s j)=(fun U=>(rows j U).part s):=by
  funext U
  have nz:(((H).rep N per j).eval U:ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
  simp only [numerator,face,←mul_assoc,mul_inv_cancel₀ nz,one_mul]

theorem flat {i j:ℕ}(ij:i≤j)(Z:X j → Poly J)(paid:Integrable Z (prior G _))(s:J.Mode):
    WilsonOriginalJointTrialHearing.read R N per (1:X i) ij Z s=
      reading R (N:=N) (fun U=>(Z U).part s) i ij:=by
  unfold WilsonOriginalJointTrialHearing.read reading
  rw [←WilsonOriginalOccupiedTransport.projected R Z paid s ij]

/-- The unpaid part of a dated charge can stay inside its signed earlier reading.
Both ordinary charges use the same original positive denominator at the stop. -/
theorem original [Fintype V] (rows:∀j,X j → Poly J)(s:J.Mode){i j:ℕ}(ij:i≤j)(top:j+1≤N)
    (young:Integrable (rows (j+1)) (prior G _))(old:Integrable (rows j) (prior G _)):
    feeAt R N per i (face R N per rows s) j=
      WilsonOriginalJointTrialHearing.fee R N per (1:X i) rows j s:=by
  have filed:=WilsonOriginalTwoFlatChronology.original R N per ij top (rows (j+1)) s
    (face R N per rows s) (fun U=>congrFun (density R N per rows s top).symm U) young
    (by rw [density R N per rows s (Nat.le_of_succ_le top)]
        exact ((Poly.get s).restrictScalars ℝ).integrable_comp old)
  rw [filed,density R N per rows s (Nat.le_of_succ_le top),WilsonOriginalJointTrialHearing.fee,dif_pos ij,
    WilsonOriginalJointTrialHearing.defect,WilsonOriginalJointTrialHearing.difference R N per _ ij _ _
      (gust_live H N per (j+1) _ young _) old,
    flat R N per ij _ (gust_live H N per (j+1) _ young _) s,flat R N per ij _ old s,
    gust_step H N per (j+1) (rows (j+1)) (Nat.lt_succ_self j),gust_base]
  rfl

end YM.Integration.WilsonReceivedChronologicalReadout
end
