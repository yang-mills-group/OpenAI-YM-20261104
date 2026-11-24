import YM.Integration.WilsonOriginalMicroscopicEntranceDoseBoard
import YM.Integration.WilsonReflectedPublicCommonEstate
import YM.Integration.WilsonReflectedPublicDoseField

/-! The paid rotated columns are exactly the regular heads of the public cutoff roster. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceDoseColumns
open Function Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Push Push.Local Marker Motion
open PhysicalNext PhysicalNext.Repeat.Legato Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi
open RG05Readout RG05Readout.Address WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder
open WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField WilsonThermometerMarchSource
open WilsonThermometerReflectedTrajectory WilsonAddressedAlignedColumn WilsonReflectedFundedHearing
open WilsonReflectedPublicGuardedColumns WilsonOriginalMicroscopicEntranceDoseBoard WilsonReflectedOpticalArm
open Extra.Histories.Relay
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){d:Fin 3→ℕ}{N per f t K:ℕ}{o:Fin 3→Site (R.family.side f per)}
  (B:Board R d N per f o t)

def amount (c:Fin 3→ℝ)(i:Fin 3):ℝ:=
  c i*charge (offer R (B.x i) (B.home i) B.live.le)

def row (c:Fin 3→ℝ)(i:Fin 3):Three G (R.family.side f per):=
  marked R (N:=N) 0 (B.motion i) (o i) (B.sight i) (B.frames i)
    ((amount R B c i:ℂ) • reduce (offer R (B.x i) (B.home i) B.live.le)) f

theorem individual (c:Fin 3→ℝ)(i:Fin 3)(A:Arm R (d i) N per f K)(fk:f≤K)(kn:K≤N)
    (Q E:Coefficient (R.family.labels.level (d i)) (R.family.side f per)){w a δ:ℝ}
    (paid:Joined R A fk kn (c i:ℂ) (row R B c i) w a δ Q E)(U:Config G (R.family.side f per)):
    Q.exponentialEntry A.o (R.family.localSection (d i)) (R.family.path.rep N per f) U=
      (c i:ℂ)*(charge (offer R (B.x i) (B.home i) B.live.le):ℂ)*
      (marked R (N:=N) 0 (B.motion i) (o i) (B.sight i) (B.frames i)
        (reduce (offer R (B.x i) (B.home i) B.live.le)) f).2.1 U:=by
  rw [←paid.regular,row,WilsonReflectedPublicDoseField.marked_real]
  change ((amount R B c i:ℝ):ℂ)*_=_
  rw [amount,Complex.ofReal_mul]

theorem original (course:∀i,Arm R (d i) N per f K)(fk:f≤K)(kn:K≤N)(c:Fin 3→ℝ)
    (Q E:∀i,Coefficient (R.family.labels.level (d i)) (R.family.side f per))
    {w a δ:Fin 3→ℝ}(paid:∀i,Joined R (course i) fk kn (c i:ℂ) (row R B c i) (w i) (a i) (δ i) (Q i) (E i))
    (s:(Stock.census (Fin 3)).Mode)(U:Config G (R.family.side f per)):
    (∏i∈s.val,(Q i).exponentialEntry (course i).o (R.family.localSection (d i)) (R.family.path.rep N per f) U)=
      head R B (fun i=>(c i:ℂ)) s U:=by
  exact Finset.prod_congr rfl (fun i _=>individual R B c i (course i) fk kn (Q i) (E i) (paid i) U)

end YM.Integration.WilsonOriginalMicroscopicEntranceDoseColumns
end
