import YM.Integration.WilsonMovingForkTerminalFile
import YM.Integration.WilsonMovingForkCensusIncidence

/-! A single marked Wilson density for all masks at a physical date. At
the upper date its slots are the fully restored fitted stencils. At lower
dates it is the complete independent compact material on the actual pins. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.WilsonMovingForkChronologicalTable
open Function Filter Finset MeasureTheory Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn
open Push Push.AbsoluteSums PhysicalNext PhysicalNext.Repeat.Legato Trace.Pilot OPE
open WilsonOriginalMixedBlockRows Pert.Asymptotics
open WilsonMovingForkPrintedFile (Board Program registered allSlots)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses units product)
open WilsonThermometerUnitFilingFourSquare (Arm)
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{n K:ℕ}{d:Fin n → ℕ}(prog:Program R d K)
  (N per:ℕ)(w:(a:Fin n) → R.family.label (d a))(ξ:Fin n → Site (R.family.side K per))
local notation "C" => R.family
local notation "J" => Stock.census (Fin n)
local notation "X" i:max => Config G ((C).side i per)

def ordinary (i:ℕ)(U:X i):Poly (J):=
  if ik:i<K then
    let b:=prog N per w ξ i ik
    WilsonOriginalTwoFlatIRMounted.value b.binder b.load b.copies (regulatorRun (C) N per i) b.wallet U
  else if eq:i=K then fun s=>∏a∈s.val,
    WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N per K (ξ a) (units R d K w a) (eq ▸ U)
  else 0

def density (i:ℕ)(U:X i):Poly (J):=fun s=>(((C).path.rep N per i).eval U:ℂ)*
  (ordinary prog N per w ξ i U).part s

theorem upper (s:(J).Mode)(U:X K):
    (ordinary prog N per w ξ K U).part s=
      ∏a∈s.val,WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N per K (ξ a) (units R d K w a) U:=by
  simp [ordinary,Poly.part]

theorem full (i:ℕ):
    (fun U=>(density prog N per w ξ i U).part (allSlots n))=
      numerator R N per i (WilsonMovingForkPrintedFile.row prog N per w ξ i):=by
  funext U
  unfold density numerator ordinary WilsonMovingForkPrintedFile.row
  by_cases ik:i<K
  · simp [ik,Poly.part]
  · by_cases eq:i=K
    · subst i
      simp [WilsonMovingForkMixedSeed.product,allSlots,Poly.part]
    · simp [ik,eq,Poly.part]
      exact Or.inr rfl

theorem dated {u j:ℕ}(uj:u ≤ j)(jn:j<N)
    (old:Integrable (density prog N per w ξ j) (prior G _))
    (young:Integrable (density prog N per w ξ (j+1)) (prior G _)):
    feeAt R N per u (WilsonMovingForkPrintedFile.row prog N per w ξ) j=
      WilsonOriginalJointTrialHearing.fee R N per (1:X u) (density prog N per w ξ) j (allSlots n):=by
  exact (WilsonMovingForkCensusIncidence.dated R uj jn (allSlots n) _ _ old young
    (full prog N per w ξ j) (full prog N per w ξ (j+1))).symm

end YM.Integration.WilsonMovingForkChronologicalTable
