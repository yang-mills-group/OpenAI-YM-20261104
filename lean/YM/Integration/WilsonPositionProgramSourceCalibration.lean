import YM.Integration.WilsonRichPrimitiveRows
import YM.Integration.ActualOriginalQPackets

/-! The true registered source inserts its prescribed fee on an actual local
field. The field coordinate is the covariance conversion of the exact filed
lattice column in the same run, including the scalar and lower grades. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramSourceCalibration
open Function Finset Lattice Wilson Labels PertExtension PertExtension.LatticePT
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop PositionX.Bare.Subcell
open RG PhysicalNext.Repeat.Legato MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve
open MS.Land MS.Menus FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop FVA2 FVAAlt2
open FVA2.Clock FVA2.Score FVA2.Based FVA2.PairCoords FVA2.Modes FVA2.Paper FVA2.Trans FVA2.ColorCode FVA2.Attend
open RegulatorIR.FVAAlt2.Lodge
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM
open ActualOriginalQReaders
open MergeProof.Accent
open FVA1
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {B : MS.Local.Physical.Deck G}

def matrix (d : ℕ) := topMatrix (R.family.localSection d) R.family.params (R.makes.sections d)
  (Block.clothes R d)

theorem inverse {d : ℕ} (v : MS.Menus.Glyph B d) :
    (matrix R v.size).inverse (covarianceSymbol G)
      (ActualOriginalDictionary.coordinates R B v.size v.grade v.2.2) =
        YM.FVAAlt2.Lobby.γ (basisR R) (YM.FVAAlt2.Lobby.owner v) :=
  WilsonRichPrimitiveRows.inverse R (YM.FVAAlt2.Lobby.owner v)

theorem coordinate {d : ℕ} (v : MS.Menus.Glyph B d) :
    (matrix R v.size).conversion (covarianceSymbol G)
      (YM.FVAAlt2.Lobby.γ (basisR R) (YM.FVAAlt2.Lobby.owner v)) =
        ActualOriginalDictionary.coordinates R B v.size v.grade v.2.2 := by
  rw [← inverse R v]
  exact LinearEquiv.apply_symm_apply _ _

variable {V : Type} (Q : MS.Land.Prescription B) (u : V → MS.Rake.Label B) (y : ℝ)

def row (i : V) (k : ℕ) (n : Side) (z : Site n) (U : Config G n) : ℂ :=
  ∑ v : MS.Menus.Glyph B (u i).h, PowerSeries.coeff k (YM.FVAAlt2.Billing.bore u Q y i v) *
    (R.family.localSection v.size).places
      ((matrix R v.size).conversion (covarianceSymbol G)
        (YM.FVAAlt2.Lobby.γ (basisR R) (YM.FVAAlt2.Lobby.owner v))) z U

theorem actual (i : V) (k : ℕ) (n : Side) (z : Site n) (U : Config G n) :
    ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) y n z U k =
      row R Q u y i k n z U := by
  rw [ActualOriginalCalibratedColumns.weighted_observable_original]
  simp only [row, coordinate R, YM.FVAAlt2.Billing.bore, PowerSeries.coeff_mk]

variable [DecidableEq V] [Fintype V] {p L n : ℕ} {hn : n ≤ L}
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V) (orders : V → ℕ)

theorem source (N : ℕ) (hL : L ≤ N) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side L p)) :
    Poly.pass ((ActualOriginalQPackets.packets Q D u y orders N).read x
      (Pert.Asymptotics.regulatorRun R.family N p L) U) =
      Poly.pass (Mach (Stock.census V) (fun i => ActualRunQlocalNativeTuple.reader D i (x i) *
        row R Q u y i (orders i) (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U)) := by
  rw [ActualOriginalQPackets.source_factor Q D u y orders N hL x U]
  simp only [actual R Q u y]

end YM.Integration.WilsonPositionProgramSourceCalibration
