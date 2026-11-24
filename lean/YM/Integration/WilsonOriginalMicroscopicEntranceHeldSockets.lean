import YM.Integration.WilsonOriginalMicroscopicEntranceHeldBoards
import YM.Integration.WilsonOriginalMicroscopicEntrancePooledSocket

/-! Identify the original physical board and the separately declared K sockets on
the three actual measured columns, using their complete filed weights. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldSockets
open Function Filter Finset MeasureTheory Lattice Wilson RG Marker PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open WilsonMeasuredPublicEntrancePanel (Panel Raw Guard charged)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReceivedCanonicalSocketPost (lit)
open WilsonOriginalMicroscopicGuardedTrial (raw)
open WilsonOriginalMicroscopicEntranceEarlier (face)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonOriginalMicroscopicEntranceHeldBoards (board)
open WilsonOriginalThermometerPalette (probe)
open Labels Source RG12 Motion QuadraticLocal
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(grades:Fin 3→ℕ){N per f K requested power t:ℕ}{B:ℝ}
  {fk:f≤K}{cut:K≤N}(A:Panel R grades N per f K fk cut requested power t B)
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)
def fee (a:Fin 3):ℂ:=WilsonMeasuredPublicEntrancePanel.charged R grades A a

def coordinate (a:Fin 3):(C).label (grades a):=
  Motion.patch ((C).labels.level (grades a)) (A.turn a)
    ((A.axis a).symm (fitted R (grades a) (A.slot a) N per (A.names a)))

/-- The upper original microscopic birth with its complete set of independently nominated fields. -/
theorem upper :
    board R (N:=N) (Raw R grades A)=fun U s=>mass (fee R grades A) s*
      (WilsonOriginalAlternativeBarePorts.offer R grades N per
        (fun a=>displayed R (grades a) (A.names a) (A.turn a))
        (fun a=>anchorAt R (A.loc a) N) lit U).part s:=by
  funext U s
  unfold board WilsonOriginalAlternativeBarePorts.offer birth Mach
  rw [Poly.part_smul,pass_fire]
  simp only [probe,lit,one_mul,WilsonMeasuredPublicEntrancePanel.Raw,Finset.prod_mul_distrib,WilsonOriginalMicroscopicEntranceDoseGrid.mass,fee,Complex.real_smul]
  ring

/-- The uncut K board is exactly the independent finite physical socket print on the same vacuum. -/
theorem original :
    (fun U s=>mass (fee R grades A) s*(WilsonOriginalMicroscopicEntranceFiling.print R grades (N:=N)
      (raw R grades N per K (pin R fk A.loc) (coordinate R grades A)) U).part s)=
      board R (N:=N) (Guard R grades A):=by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le fk
  funext U s
  have paid:Guard R grades A s U=mass (fee R grades A) s*(units R grades (f+n) s*
      face (raw R grades N per (f+n) (pin R fk A.loc) (coordinate R grades A)) s U):=
    WilsonOriginalMicroscopicEntrancePooledSocket.filed R grades cut A.loc (coordinate R grades A) s (fee R grades A) U
  change mass (fee R grades A) s*((R.family.path.rep N per (f+n)).eval U • _) =
    (R.family.path.rep N per (f+n)).eval U • Guard R grades A s U
  rw [paid]
  simp only [Complex.real_smul]
  ring

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldSockets
end
