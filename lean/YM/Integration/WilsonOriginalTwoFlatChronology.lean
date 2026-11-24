import YM.Integration.WilsonOriginalTwoFlatSuccessor
import YM.Integration.WilsonOriginalTwoFlatTelescope

/-! Insert an actual all-face posted successor into the scalar chronological
debit, before forming the connected observable at the older stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatChronology
open Function Filter Finset MeasureTheory Lattice RG Wilson Marker
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(N per:ℕ)
local notation "H" => R.family.path
local notation "X" j:max => Config G (R.family.side j per)

private theorem across {i b j:ℕ}(f:X j→ℂ)(ib:i≤b)(bj:b≤j):
    gust H N per j f i (ib.trans bj)=gust H N per b (gust H N per j f b bj) i ib:=by
  induction ib using Nat.decreasingInduction with
  | self=>rw [gust_base]
  | of_succ k kb ih=>rw [gust_step H N per j f (kb.trans_le bj),gust_step H N per b _ kb,ih]

theorem original {V:Type}[DecidableEq V][Fintype V]{J:Census V}
    {i j:ℕ}(ij:i≤j)(top:j+1≤N)(Y:X (j+1)→Poly J)(s:J.Mode)
    (rows:∀t:ℕ,X t→ℂ)(input:∀U,(Y U).part s=numerator R N per (j+1) (rows (j+1)) U)
    (good:Integrable Y (prior G _))(old:Integrable (numerator R N per j (rows j)) (prior G _)):
    feeAt R N per i rows j=reading R (N:=N) (fun U=>(LocalComparison.actualPush R.family N per j Y U).part s) i ij-
      reading R (N:=N) (numerator R N per j (rows j)) i ij:=by
  have upper:=funext input
  have young:Integrable (numerator R N per (j+1) (rows (j+1))) (prior G _):=by
    rw [←upper];exact ((Poly.get s).restrictScalars ℝ).integrable_comp good
  have first:(fun U=>(LocalComparison.actualPush R.family N per j Y U).part s)=
      gust H N per (j+1) (numerator R N per (j+1) (rows (j+1))) j (Nat.le_succ j):=by
    calc _=(fun U=>(gust H N per (j+1) Y j (Nat.le_succ j) U).part s):=by
           rw [gust_step H N per (j+1) Y (Nat.lt_succ_self j),gust_base];rfl
         _=_:=by rw [WilsonOriginalOccupiedTransport.projected R Y good s (Nat.le_succ j),upper]
  rw [feeAt,dif_pos ij,edge R N per ij top rows old young,first]
  unfold reading
  rw [across R N per (numerator R N per (j+1) (rows (j+1))) ij (Nat.le_succ j)]

end YM.Integration.WilsonOriginalTwoFlatChronology
end
