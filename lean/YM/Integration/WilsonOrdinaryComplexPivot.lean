import YM.Integration.WilsonOrdinaryCutBilinear
import YM.Integration.WilsonOrdinaryPhaseRecovery

/-! The actual complex field selected on the original physical theory by
an independently prescribed microscopic source, including both quadratures
and arbitrarily signed finite combinations. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryComplexPivot
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


open WilsonOrdinaryCutBilinear WilsonOrdinaryPhaseRecovery
local notation "D!" => RG17.Free R.family d

/-- The same originally bought second-site source, with the native
anti-linear adjoint before its complex linear reporting and cutoff maps. -/
def right (r : ℝ) (E : D!→L[ℂ]R.family.label d) (z : UVIndex) :
    D!→ₛₗ[starRingEnd ℂ]R.family.label d :=
  ((transport R L d r z).comp E.toLinearMap).comp
    ((Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) d timeAxis)

variable (F) (J : ℝ→tower S)

theorem original (present : Pier.Lair.Present F J) (shift : L.shift=(fun _ _=>LinearEquiv.refl ..))
    (funds : Pier.Lair.Paying F (Pier.Lair.tender F L J) d) :
    ∃ (δ : ℝ),0<δ ∧ ∃ (p : ℕ) (c : ℝ) (E : ℝ→(D!→L[ℂ]R.family.label d)),0≤c ∧
      ∀ᶠ r in trail, (∀ v,master L d r (E r v)=J r d v) ∧
        ‖E r‖≤c*R.family.path.levels.clock.hatBeta (L.level r)^p ∧
        ∃ D : (D!→L[ℝ]ℝ)→ₗ[ℝ]S.Field d,
          ∀ (h : ℕ) (z : UVIndex) (x y : Site (R.family.side z.1 z.2)),
            ∃ X : R.family.label h→ₗ[ℂ]S.Field d, ∀ a,
              let charge := ear (pairing R d h z x y) (right L d r (E r) z) a
              X a=D charge ∧ δ*‖(J r d).symm (X a)‖≤‖charge‖ ∧
              (∀ v,mixed F J d r r ((J r d).symm (X a)) v =
                (WilsonOrdinaryCutBilinear.integral R d h z x y a (RG17.atRef L d r z (E r (adjoint R d v)))).re) ∧
              ∀ t,(∀ v,mixed F J d r r ((J r d).symm t) v =
                (WilsonOrdinaryCutBilinear.integral R d h z x y a (RG17.atRef L d r z (E r (adjoint R d v)))).re) → t=X a := by
  obtain ⟨δ,hδ,hD⟩ := WilsonOrdinaryPositionDecoder.original F d J present
  obtain ⟨p,c,E,hc,hE⟩ := WilsonMacroscopicMatchedSection.purchased F L J shift d funds
  refine ⟨δ,hδ,p,c,E,hc,?_⟩
  filter_upwards [hD,hE] with r hd he
  obtain ⟨D,read,bill,only⟩ := hd
  refine ⟨he.1,he.2,D,?_⟩
  intro h z x y
  let K := pairing R d h z x y
  let T := right L d r (E r) z
  obtain ⟨X,hX⟩ := recover K F J d r D read only T
  refine ⟨X,?_⟩
  intro a
  refine ⟨hX a,?_,?_,?_⟩
  · rw [hX]; exact bill _
  · intro v; rw [hX]; exact read (ear K T a) v
  · intro t heard; rw [hX]; exact only (ear K T a) t heard

end YM.Integration.WilsonOrdinaryComplexPivot
