import YM.Integration.WilsonIndependentMatchedBufferedVacuum
import YM.Integration.WilsonIndependentMatchedFittedSeat
import YM.Integration.WilsonIndependentMatchedCoverGrade
import YM.Integration.WilsonPositionProgramTrialHomeDose

/-! Identify the complete ordinary fitted side on the inherited N vacuum
with the product running under its genuine compensated reporting coordinates. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedAccruedFaces
open Function Finset Matrix Lattice Wilson RG Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonIndependentMatchedReportedProxy (passport sectionSeal)
open WilsonIndependentMatchedFittedSeat (dose receiving)
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonMarkedIndependentNormalizedElection (normalized)
open scoped BigOperators Classical
variable {G:Gauge}{h D k e u n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}
    {p:h<D}{v:Rails h k u e}{E W U V:Credit}

local notation "Cuts" => CutsP H T p v E W U V
local notation "Q" => fun _:Fin (n+1)=>sectionSeal T p

def paidVector (X:Fin (n+1)→Cuts)(a:Fin (n+1)→ℝ):Herit Q:=
  fun s=>publicDose (sectionSeal T p) (X s) (a s)

/-- All genuine fitted factors before taking a joint conditional expectation. -/
def product (X:Fin (n+1)→Cuts)(a:Fin (n+1)→ℝ)(φ:Fin (n+1)→Rarity D)(y:ℝ)(o:CellR):Era G ℝ:=
  MassP G ℝ n (fun s=>receiving (X s) (a s) (φ s) y o (X s).i)

theorem face (X:Fin (n+1)→Cuts)(a:Fin (n+1)→ℝ)(φ:Fin (n+1)→Rarity D)(y:ℝ)(o:CellR)
    (course:∀s,(X s).vesselsC=(X 0).vesselsC)
    (bottom:∀s,(X s).m=(X 0).m)(birth:∀s,(X s).ceilC=(X 0).ceilC)(prior:∀s,(X s).N=(X 0).N):
    Ashore Q (X 0).ax (X 0).tx φ
      (normalized (X 0).ax (X 0).tx Q (paidVector X a) (X 0).m (X 0).N)
      (X 0).m (X 0).ceilC (X 0).N y o=product X a φ y o:=by
  have lev (s:Fin (n+1)):(X s).ax=(X 0).ax:=congrArg (fun R=>R.draws) (course s)
  have chart (s:Fin (n+1)):(X s).tx=(X 0).tx:=congrArg (fun R=>R.paid) (course s)
  have exactDose (s:Fin (n+1)):
      normalized (X 0).ax (X 0).tx Q (paidVector X a) (X 0).m (X 0).N s=dose (X s) (a s):=by
    change PermuteLens _ _ _ _ _ (publicDose _ _ _)=_
    rw [←lev s,←chart s,←prior s,←bottom s]
    exact (WilsonPositionProgramTrialHomeDose.original (sectionSeal T p) (X s) (a s)).1

  apply congrArg (MassP G ℝ n)
  funext s
  change locale o ((sectionSeal T p).spins _ _ _ _ _ _ _
    (normalized (X 0).ax (X 0).tx Q (paidVector X a) _ _ s))=
    locale o ((sectionSeal T p).spins (X s).ax (X s).tx _ (X s).m (X s).ceilC (X s).N _ _)
  rw [exactDose s,lev s,chart s,prior s,bottom s,birth s]
  rfl

theorem authentic (X:Fin (n+1)→Cuts)(a:Fin (n+1)→ℝ)(φ:Fin (n+1)→Rarity D)(y:ℝ)(o:CellR):Auth (capP Q) (product X a φ y o):=by
  have gifted (s:Fin (n+1)):Auth h (receiving (X s) (a s) (φ s) y o (X s).i):=by
    exact (WilsonIndependentMatchedCoveredSeats.wired (X s).vesselsC (sectionSeal T p) (passport (X s))
      (φ s) (dose (X s) (a s)) (X s).m (X s).N (X s).i (X s).ha ((X s).hc.trans (X s).hn) y o).1 _ le_rfl
  exact manCo _ (fun _:Fin (n+1)=>h) gifted

theorem original (X:Fin (n+1)→Cuts)(a:Fin (n+1)→ℝ)(φ:Fin (n+1)→Rarity D)(y:ℝ)(o:CellR)
    (stop:ℕ)(older:stop ≤ (X 0).m)(course:∀s,(X s).vesselsC=(X 0).vesselsC)
    (bottom:∀s,(X s).m=(X 0).m)(birth:∀s,(X s).ceilC=(X 0).ceilC)(prior:∀s,(X s).N=(X 0).N):
    WilsonIndependentMatchedBufferedVacuum.stopped (X 0).ax (X 0).tx Q φ (paidVector X a)
      (X 0).m (X 0).ceilC (X 0).N stop y o=
    cruises (X 0).ax (X 0).tx (X 0).N ((n+1)*k) (X 0).ceilC stop (product X a φ y o):=by
  have fits:capP Q ≤ (n+1)*k:=by
    simpa [capP,asp,sectionSeal] using Nat.mul_le_mul_left (n+1) v.hk
  unfold WilsonIndependentMatchedBufferedVacuum.stopped WilsonIndependentMatchedRestartVacuum.reading
  change cruises _ _ _ _ _ _ (cruises _ _ _ _ _ _ (Ashore _ _ _ _ _ _ _ _ _ _))=_
  rw [face X a φ y o course bottom birth prior,←cruisesMore _ _ _ older (Nat.le_add_right _ _)]
  exact WilsonIndependentMatchedCoverGrade.carried _ _ (X 0).vesselsC.hG (X 0).vesselsC.green
    (older.trans (Nat.le_add_right _ _)) ((X 0).hc.trans (X 0).hn) _ (authentic X a φ y o) fits

end YM.Integration.WilsonIndependentMatchedAccruedFaces
