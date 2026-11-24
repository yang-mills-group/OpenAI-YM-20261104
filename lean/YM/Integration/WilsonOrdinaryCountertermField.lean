import YM.Integration.WilsonOrdinaryPricedGlyph

/-! The actual prescribed finite counterterm row, with all lower engineering
grades and both phases, as one field on the originally selected positive
theory. This is a regulator-level calibration, before the remaining
asymptotic identification on independent profiles. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryCountertermField
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep WilsonOrdinaryFourGram
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryMeasuredMarch
open Cells Push.GridApprox
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

open WilsonOrdinaryHomogeneousDetectors

open MS MS.Menus MS.Local.Physical FVAAlt2 FVA2 Extra.Histories
open RegulatorIR.FVAAlt2.Lodge WilsonFactoryFiledGlyphs WilsonOrdinaryUltravioletPair
open WilsonOrdinaryPositionDecoder WilsonOrdinaryHomogeneousDetectors
variable {F : Final R.family f S} (L : Layout F) (d : ℕ)
variable {B : Deck G}

open MS.Land MS.Rake MS.Book MS.Book.Program
open FVAAlt2.Lobby FVAAlt2.Billing PowerSeries
open MeasureTheory
open WilsonOrdinaryPricedGlyph
variable (F) (J : ℝ→tower S)
local notation "D!" => RG17.Free R.family d

/-- Every independent prescribed coefficient field on this same physical
bank, including all its genuinely lower-height terms. A single reporting
section is fixed before the entire prescription, time, nominal grade,
coefficient, cutoff, period, and two sites. -/
theorem original (present : Pier.Lair.Present F J) (shift : L.shift=(fun _ _=>LinearEquiv.refl ..))
    (funds : Pier.Lair.Paying F (Pier.Lair.tender F L J) d) :
    ∃ (p₀ : ℕ) (c : ℝ) (E : ℝ→(D!→L[ℂ]R.family.label d)),0≤c ∧
      ∀ᶠ r in trail, (∀ v,master L d r (E r v)=J r d v) ∧
        ‖E r‖≤c*R.family.path.levels.clock.hatBeta (L.level r)^p₀ ∧
        ∀ {B : Deck G} {W : Type} (Q : MS.Land.Prescription B) (y : ℝ)
          (p : W→MS.Rake.Label B) (ε : ℝ) (i : W) (k : ℕ) (z : UVIndex) (u : ℝ)
          (x t : Site (R.family.side z.1 z.2)),
          ∃ q : S.Field d, ∀ v : D!, mixed F J d r r ((J r d).symm q) v=
            (Wilson.moment (R.family.beta z.1 z.2) (fun U=>WilsonOrdinaryPricedGlyph.field R Q y p ε i k z u x U*
              R.family.O z.1 z.2 (RG17.atRef L d r z (E r (adjoint R d v))) t U)).re := by
  obtain ⟨_,_,p₀,c,E,hc,ready⟩ := WilsonOrdinaryComplexPivot.original
    (F:=F) (J:=J) (L:=L) (d:=d) present shift funds
  refine ⟨p₀,c,E,hc,?_⟩
  filter_upwards [ready] with r measured
  obtain ⟨lift,bill,D,stages⟩ := measured
  refine ⟨lift,bill,?_⟩
  intro B W Q y p ε i k z u x t
  have every (v : Glyph B (p i).h) := stages (owner v).h z x t
  choose X hx using every
  let a (v : Glyph B (p i).h) := amplitude R Q y p ε i k z v • ledger R (owner v) z.1 z.2 u
  refine ⟨∑v,X v (a v),?_⟩
  intro w
  let b := RG17.atRef L d r z (E r (adjoint R d w))
  have receipt (v : Glyph B (p i).h) := (hx v (a v)).2.2.1 w
  rw [WilsonOrdinaryPricedGlyph.measured (R:=R) (Q:=Q) (y:=y) (p:=p) (ε:=ε) (i:=i) (k:=k) (z:=z) (d:=d) u x t b]
  simp only [map_sum,_root_.sum_apply,Complex.re_sum]
  exact Finset.sum_congr rfl fun v _=>receipt v

end YM.Integration.WilsonOrdinaryCountertermField
