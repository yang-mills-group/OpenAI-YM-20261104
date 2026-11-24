import YM.Integration.WilsonAddressedWeakStationGram
import YM.Integration.WilsonAddressedWeakFiledTargets
import YM.Integration.WilsonAddressedWeakActualExaminer

/-! Identify the detector's charged replicated moments with the original Wilson cylinder,
at the actual independently addressed cutoff sites and for both proper faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakDetectorExpense
open Function Set Filter MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open Trace Trace.Pilot PhysMS XSpace XSpace.Normalize
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue Marker Push.Corrected Marks
open WilsonAddressedWeakCalibration WilsonAddressedWeakPointCells WilsonAddressedWeakCorrectedCylinder
open Next.Rank Next.Rank.Station Next.Rank.Ship
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {B:Local.Physical.Deck G} {O:Booked B} (M:MS_Data G O)
variable {D k N p j:ℕ}
local notation "A" => R.family.path.levels

theorem original (b:ℝ) (live:k≤N) (hj:j≤N) (d:Fin 2→ℕ) (x:Points 2)
    (a e:Glyph B D) (μ:ℝ) (Y:(i:Fin 2)→Palette R.family (d i)) (r:(i:Fin 2)→Emblems R.family (d i))
    (s:Finset (Fin 2)) (nonempty:s.Nonempty) :
    let χ:=width (A) b k
    let gr:χ≤k:=(wider (A) b k).trans (before ..)
    let ρ:=gap (A) b k
    let z:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
    let v:=projected R (p:=p) live ρ (gap_pos ..) x
    let tags:=WilsonAddressedWeakMaxwellPositions.tags R B ![a,e]
    let field:=WilsonThermometerIntrinsicRoster.source R d z Y r live
    ∀ fit:Station.Fit (A) b k v,
      WilsonAddressedWeakRankHearing.fee R M (p:=p) gr live hj d ρ (gap_pos ..) x a e μ Y r s =
        (Ship.yard R.family b live p).rootTest (R.family.beta N p)
          (fun U=>(Read.cylinder (Ship.targets R.family tags fit) field U).part (Next.Rank.Glyph.scene s)) := by
  intro χ gr ρ z v tags field fit
  let m (i:Fin 2):=WilsonAddressedWeakShapeFees.mean M (![a,e] i) v i μ
  let q:=MSDeckProbeGram.raw M ![a,e] v μ 0
  let P:=WilsonAddressedWeakPackedCertificate.inserted R d z Y r live m q
  obtain ⟨good,target⟩:=WilsonAddressedWeakFiledTargets.targets R b ![a,e] live x fit
  have eq (U):Marks.part (P U) s=(Read.cylinder (Ship.targets R.family tags fit) field U).part (Next.Rank.Glyph.scene s):=by
    have p:=WilsonAddressedWeakPackedCertificate.coefficients R d z Y r live m q U
    have w:=WilsonAddressedWeakMaxwellPositions.cylinder R M field U ![a,e] v good μ
    change _=(Read.cylinder (Ship.targets R.family (WilsonAddressedWeakMaxwellPositions.tags R B ![a,e]) fit) field U).part _
    rw [target]
    have choices:∀ s:Finset (Fin 2),s.Nonempty → s={0} ∨ s={1} ∨ s={0,1}:=by decide
    rcases choices s nonempty with rfl|rfl|rfl
    · exact (p.1 0).trans (w.1 0).symm
    · exact (p.1 1).trans (w.1 1).symm
    · exact p.2.trans w.2.symm
  change ‖WilsonAddressedWeakCompensatedHearing.report R gr live d z Y r m q hj s‖^_ = _
  rw [WilsonAddressedWeakCompensatedHearing.measured]
  change WilsonAddressedWeakPackedCertificate.expense R d z Y r live m q (Ship.yard R.family b live p) s = _
  unfold WilsonAddressedWeakPackedCertificate.expense Tiling.rootTest
  simp_rw [Marks.folded]
  dsimp only [P] at eq
  simp_rw [eq]

end YM.Integration.WilsonAddressedWeakDetectorExpense
