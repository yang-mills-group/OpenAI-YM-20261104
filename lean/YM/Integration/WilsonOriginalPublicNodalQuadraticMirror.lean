import YM.Integration.WilsonOriginalObservedRoseCorrectedWords
import YM.Integration.WilsonMovingForkPrintedFile
import YM.Integration.WilsonReflectedMixedIntrinsicAxis
import YM.Integration.WilsonOriginalPublicNodalDeployedVote

/-! A repeated physical slot in a reflected test retains its actual filed inverse
and label, including the unit. All geometry enters after evaluating that inverse. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalQuadraticMirror
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonMovingForkPrintedFile (Program row)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonMovingForkMixedSeed (units doses)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonOriginalPublicNodalDeployedVote (deployed)
open scoped Classical BigOperators
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G){n a K:ℕ}(d:Fin n→ℕ)
    (file:Filed R d K)(pick:Fin a→Fin n)(prog:Program R (d∘pick) K)

/-- File any subpanel, with repeated arms allowed, using the original admitted
full K axes and the real printed program of that panel. -/
def print:Filed R (d∘pick) K where
  station:=file.station∘pick
  target:=file.target
  before:=fun j=>file.before (pick j)
  A:=fun N per j=>file.A N per (pick j)
  arrived:=fun N per before j e=>file.arrived N per before (pick j) e
  row:=row prog
  seed:=by
    intro N per live w ξ
    funext U
    simp [row]

variable (N per:ℕ)(Y:∀i,R.family.label (d i))(τ:Fin a→Motion)

/-- The field in a new printed chamber uses the same commissioned vote even
when both copies come from the same arm and are independently moved. -/
theorem filed (j:Fin a):
    (print R d file pick prog).A N per j=file.A N per (pick j) ∧
    votes R (d∘pick) (N:=N) (per:=per) (print R d file pick prog) (fun t=>Y (pick t)) τ j=
      votes R d (N:=N) (per:=per) file Y (fun _=>τ j) (pick j) ∧
    deployed R ((d∘pick) j) K (N,per)
      (votes R (d∘pick) (N:=N) (per:=per) (print R d file pick prog) (fun t=>Y (pick t)) τ j)=
      deployed R (d (pick j)) K (N,per)
        (votes R d (N:=N) (per:=per) file Y (fun _=>τ j) (pick j)):=⟨rfl,rfl,rfl⟩

/-- An independent original file at these same stations also measures the
same axes, by its own authentic `Arrived` receipt on the physical N history. -/
theorem incumbent (other:Filed R (d∘pick) K)(same:∀j,other.station j=file.station (pick j))
    (ref:∀j,R.family.ref (d (pick j))≤file.station (pick j))(live:K<N):
    ∀j,other.A N per j=file.A N per (pick j):=by
  intro j
  have prior (x:R.family.label (d (pick j))):Arrived R (d (pick j)) (file.station (pick j)) K N per
      other.target (file.before (pick j)) live.le (1/32) (other.A N per j) x:=by
    simpa only [same j,comp_apply] using other.arrived N per live j x
  exact WilsonReflectedMixedIntrinsicAxis.unique R (ref j) (file.before (pick j)) live.le prior
    (file.arrived N per live (pick j))

theorem heard (other:Filed R (d∘pick) K)(same:∀j,other.station j=file.station (pick j))
    (ref:∀j,R.family.ref (d (pick j))≤file.station (pick j))(live:K<N)(j:Fin a):
    votes R (d∘pick) (N:=N) (per:=per) other (fun t=>Y (pick t)) τ j=
      votes R d (N:=N) (per:=per) file Y (fun _=>τ j) (pick j):=by
  simp only [votes,units,doses,comp_apply]
  rw [same j,incumbent R d file pick N per other same ref live j]
  rfl

end YM.Integration.WilsonOriginalPublicNodalQuadraticMirror
