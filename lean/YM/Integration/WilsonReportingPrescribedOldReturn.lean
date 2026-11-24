import YM.Integration.WilsonReportingPrescribedOldSource
import YM.Integration.WilsonReportHarvestPlatedShift

/-! The original independently prescribed mark inside the actual nonbare Wilson return. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldReturn

open Function Finset Lattice Wilson RG Source Labels Marker FVA1
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open MergeProof MergeProof.Accent MergeProof.Replicums RG3.Held RG3.Script.Picnic
open Extraction Table Spec RG12 RG17 MS MS.Menus MS.Local.Physical
open WilsonMacroscopicForwardTransfer Push.GridApprox WilsonTranslatedFactory
open WilsonReportingPrescribedOldGrade WilsonReportingPrescribedOldGlyph
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : Layout F) {B : Deck G} {h : ℕ} (v : Glyph B h)
  {N per : ℕ} (r : ℝ) (live : L.level r < N) (fee : ℂ)

abbrev label := atRef L v.size r (N,per) (filed R F L v r fee)

abbrev returned (z : Site (R.family.side N per)) (U : Config G (R.family.side (L.level r) per)) : ℂ :=
  actualTransport R.family (N:=N) (R.family.O N per (label R F L v (N:=N) (per:=per) r fee) z) live.le U

/-- The actual signed correction of the same factory entry on the unaltered old gas. -/
def credit (z : Site (R.family.side N per)) (U : Config G (R.family.side (L.level r) per)) : ℂ :=
  let y := (R.family.S.toDepth live.le per).parent z
  let Q := entry R.makes live.le y ((R.family.factory v.size N per).terminal.symm (label R F L v (N:=N) (per:=per) r fee))
  ((R.family.S.a (L.level r) : ℂ)^v.size)⁻¹ *
    WilsonMatrixTicketLanesReportedCredit.remainder R Q (R.family.path.rep N per (L.level r)) y U

/-- The displacement of this very fine site, measured in the original Wilson conditional. -/
abbrev shifted (z : Site (R.family.side N per)) (U : Config G (R.family.side (L.level r) per)) : ℂ :=
  WilsonReportHarvestPlatedShift.movement R live (label R F L v (N:=N) (per:=per) r fee)
    (anchor R.family.S per live.le ((R.family.S.toDepth live.le per).parent z)) z U

theorem measured (age : R.family.ref v.size ≤ L.level r) (z : Site (R.family.side N per))
    (U : Config G (R.family.side (L.level r) per)) :
    observed R F L v r fee N per ((R.family.S.toDepth live.le per).parent z) U =
      returned R F L v r live fee z U - credit R F L v r live fee z U - shifted R F L v r live fee z U := by
  have transported := WilsonReportHarvestPlatedShift.original R F L r (filed R F L v r fee) age live z U
  have entered := WilsonMatrixTicketLanesReportedPlating.measured R F L v.size r (filed R F L v r fee)
    N per age live.le ((R.family.S.toDepth live.le per).parent z) U
  dsimp only at transported
  rw [← entered] at transported
  change returned R F L v r live fee z U =
    observed R F L v r fee N per ((R.family.S.toDepth live.le per).parent z) U +
      credit R F L v r live fee z U + shifted R F L v r live fee z U at transported
  rw [transported]
  ring

variable (Q : MS.Land.Prescription B)

def column (u : MS.Rake.Label B) (μ : ℝ) (k : ℕ) (z : Site (R.family.side N per))
    (U : Config G (R.family.side (L.level r) per)) : ℂ :=
  let g := R.family.path.levels.clock.hatCoupling (L.level r)
  let w := WilsonReportingPrescribedOldSource.fee Q u μ k
  let y := (R.family.S.toDepth live.le per).parent z
  ∑ v : Glyph B u.h,
    ((scale R F L u.h r)⁻¹ * (((g^v.grade : ℝ) : ℂ) *
      (returned R F L v r live (w v) z U - credit R F L v r live (w v) z U -
        shifted R F L v r live (w v) z U)) -
      w v * (R.family.localSection v.size).places (lower R v g) y U)

theorem prescribed (u : MS.Rake.Label B) (μ : ℝ) (k : ℕ) (hr : 0 < r)
    (age : ∀ v : Glyph B u.h, R.family.ref v.size ≤ L.level r) (z : Site (R.family.side N per))
    (U : Config G (R.family.side (L.level r) per)) :
    ActualOriginalCalibratedColumns.weightedObservable R B Q u μ (R.family.side (L.level r) per)
      ((R.family.S.toDepth live.le per).parent z) U k = column R F L r live Q u μ k z U := by
  rw [WilsonReportingPrescribedOldSource.prescribed R F L Q u μ k r hr N per age live.le]
  unfold WilsonReportingPrescribedOldSource.column column
  apply Finset.sum_congr rfl
  intro v _
  rw [measured R F L v r live _ (age v) z U]

variable {n : ℕ} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

/-- Complete old marked source at a strict nonbare date, with every original
reader, Wilson singleton return, old gas and common gauge field. -/
theorem original (hG : G.Simple) (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)
    (hr : 0 < r) {hn : n ≤ L.level r} (D : ActualRunQlocalNativeTuple.Datum R per (L.level r) n hn V)
    (age : ∀ s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ L.level r)
    (z : V → Site (R.family.side N per))
    (placed : ∀ i, (R.family.S.toDepth live.le per).parent (z i) = ActualRunQlocalNativeTuple.root D i)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side (L.level r) per)) :
    ((ActualOriginalQInput.input Q D u μ orders hG N live.le).leaf x).density U =
      birth (Stock.census V) (R.family.path.rep N per (L.level r))
        (fun i W => ActualRunQlocalNativeTuple.reader D i (x i) *
          column R F L r live Q (u i) μ (orders i) (z i) W) U := by
  rw [ActualOriginalQInput.density_full Q D u μ orders hG N live.le age x U]
  congr 2
  funext i W
  rw [← placed i, prescribed R F L r live Q (u i) μ (orders i) hr (fun v => age ⟨i,v⟩) (z i) W]

end YM.Integration.WilsonReportingPrescribedOldReturn
