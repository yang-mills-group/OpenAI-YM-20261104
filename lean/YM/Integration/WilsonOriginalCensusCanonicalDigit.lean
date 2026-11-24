import YM.Integration.WilsonOriginalCensusCanonicalKinetic
import YM.Integration.WilsonOriginalCensusFiniteForest
import YM.Integration.WilsonNeutralTwoPrintPathStart

/-! The first actual child tuple on each compatible lifted input. The finite
original forest and cover regulator share the nominated seed and kinetic ratio. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalDigit
open Function Filter Finset Lattice Wilson RG Source Labels WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Winding
open Laurent Bloch Exterior Tree WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open PhysicalNext.Repeat.Legato Next.Foundations FormalBulk08 Pressure
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonReceivedCanonicalSocketSeed WilsonReceivedCanonicalVerseBasis WilsonReceivedCanonicalVerseRegister
open WilsonOriginalFoldedMarkedRightColumn WilsonOriginalStarSceneWords
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathStart (returned)
open scoped Classical BigOperators

variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V](R:Run G)
  (d:V→ℕ){h:V→ℕ}(pt:V→Chamber)(q:(j:V)→Choice R d j)(N i per:ℕ)
local notation "κ" => fun j=>contact (h j)
local notation "S" => WilsonVacuumPreResetStationaryChange.step R i per
local notation "front" y:max => start R d (κ) pt q y
local notation "L" => R.family.path.levels
local notation "P" => loose R.family.path.levels i
local notation "times" => ratioHigh (L) R.metals.O N i

theorem placed (y:V → Lattice.Cover)(cell:V→Site (P).L)(J₀:Finset V):
    WilsonOriginalCensusCanonicalKinetic.connected (h:=h) R d pt q N i per (repeatF (S))
      (times) (chartIn (P) y cell) J₀=
    flash (pPly (present h) J₀ (returned R d (κ) pt N i (coarse R i per) q y cell J₀)):=by
  apply congrArg (fun U=>flash (pPly (present h) J₀ U))
  exact WilsonOriginalCensusFiniteForest.original R N i per d (front (chartIn (P) y cell)) (times) J₀

theorem successor (cells:Digits (L) V)(y:V → Lattice.Cover)(J₀:Finset V):
    fixed R d (κ) pt N (i+1) i cells q y J₀=
      logO (L) R.metals.O i N (front (chartIn (P) y (cells i))) d J₀:=by
  unfold fixed
  rw [show i+1-i=1 by omega]
  rfl

theorem original (simple:G.Simple)(sale:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices sale R.kit)(Q:ℕ):
    ∀ᶠ i:ℕ in atTop, ∀(J₀:Finset V)(e r:ℕ),e≤Q → ∃C σ:ℝ,0≤C ∧ 0<σ ∧
    ∀N,i<N → ∀(q:(j:V)→Choice R d j)(per:ℕ)(y:V → Lattice.Cover)(cells:Digits (L) V),
    MarkU y J₀ (returned R d (κ) pt N i (coarse R i per) q y (cells i) J₀ e r)
      ((fixed R d (κ) pt N (i+1) i cells q y J₀).2 e r) σ C:=by
  filter_upwards [WilsonNeutralTwoPrintPathStart.original R d (κ) pt simple sale funded Q] with i bill
  intro J₀ e r he
  obtain ⟨C,σ,cn,sp,admit⟩:=bill J₀ e r he
  refine ⟨C,σ,cn,sp,?_⟩
  intro N live seed per y cells
  rw [successor]
  exact admit N live seed (coarse R i per) y (cells i)

end YM.Integration.WilsonOriginalCensusCanonicalDigit
end
