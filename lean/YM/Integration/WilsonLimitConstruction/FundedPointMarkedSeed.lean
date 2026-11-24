import YM.Integration.FundedOriginalMarkedInput
import YM.Integration.ActualOriginalQPointDatum

/-! The actually calibrated same-level point source has a single complete
finite bank before its period, cutoff and independently assigned lattice roots. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPointMarkedSeed
open Function Finset Lattice Wilson RG Source Marker PhysicalNext.Repeat.Legato
open ComparisonDensity.Address RG05Readout RG05Readout.Native RG05Readout.Flatten
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open OriginalMarkedSourceComet OriginalSourceJetAddresses IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (R : Run G)
    {B : MS.Local.Physical.Deck G} (P : MS.Land.Prescription B)
    (grades weights : V→ℕ) (labs : V→MS.Rake.Label B) (μ : ℝ) (orders : V→ℕ)
    (normal : V→ℂ) (quadrature : V→Bool)

abbrev datum (per b : ℕ) (o : V→Site (R.family.side b per)) :=
  ActualOriginalQPointDatum.datum R per b o grades weights

abbrev reference := datum R grades weights 0 0 (fun _=>0)

def source :=
  FundedOriginalMarkedInput.chosen P (reference R grades weights) labs μ orders normal quadrature

omit [DecidableEq V] [Fintype V] in
theorem same (per b : ℕ) (o : V→Site (R.family.side b per)) :
    FundedOriginalMarkedInput.chosen P (datum R grades weights per b o) labs μ orders normal quadrature =
      source R P grades weights labs μ orders normal quadrature := by
  funext i s
  unfold source
  simp only [datum,reference,FundedOriginalMarkedInput.chosen,ActualOriginalQPointDatum.constant_eq]
  simp only [ActualOriginalQPointDatum.datum,ratio_one,OriginalMarkedSourceComet.place,originR]

theorem invoice (k : V→ℕ) (e : ℕ) (w : ℝ) (per b : ℕ) (o : V→Site (R.family.side b per)) :
    bill (FundedOriginalMarkedInput.chosen P (datum R grades weights per b o) labs μ orders normal quadrature)
      k e w = bill (source R P grades weights labs μ orders normal quadrature) k e w :=
  congrArg (fun seeds=>bill seeds k e w) (same R P grades weights labs μ orders normal quadrature per b o)

omit [DecidableEq V] [Fintype V] in
theorem measurements (per b : ℕ) (o : V→Site (R.family.side b per)) (i : V) :
    let physical := datum R grades weights per b o
    ActualRunQlocalNativeTuple.root physical i=o i ∧
    ∀ f : (ActualRunQlocalNativeTuple.orbit physical i).Mood,ActualRunQlocalNativeTuple.reader physical i f=f.val 0 :=
  ⟨ActualOriginalQPointDatum.root_eq R per b o grades weights i,
    ActualOriginalQPointDatum.reader_eq R per b o grades weights i⟩

end YM.Integration.WilsonLimitConstruction.FundedPointMarkedSeed
end
