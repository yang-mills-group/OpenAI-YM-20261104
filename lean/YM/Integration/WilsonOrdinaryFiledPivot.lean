import YM.Integration.WilsonOrdinaryPositionDecoder
import YM.Integration.WilsonFactoryFiledGlyphs
import YM.Integration.WilsonMacroscopicMatchedSection

/-! The measured calibration of independently named graded glyphs. At
every true regulator and coupling the same genuine physical decoder
receives the normalized original Wilson two-mark read of the independent
filed glyph with its honest caller-selected right field. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryFiledPivot
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

private def site (r : ℝ) (z : UVIndex) (j : Fin 2) : Site (R.family.side z.1 z.2) :=
  wrap (R.family.side z.1 z.2) (address (R.family.S.a z.1) (r • detectors) j)

/-- One literal normalized finite Wilson read with the fully filed independent
first mark and the second *already assigned* actual physical charge. -/
def row (r : ℝ) (v : MS.Rake.Label B) (u : ℝ) (z : UVIndex) (w : R.family.label d) : ℝ :=
  (Wilson.moment (R.family.beta z.1 z.2) (fun U=>
    R.family.O z.1 z.2 (ledger R v z.1 z.2 u) (site (R:=R) r z 0) U *
    R.family.O z.1 z.2 (RG17.atRef L d r z w) (site (R:=R) r z 1) U)).re

/-- The independently named Γ remains in each native normalized elementary
joint column. Its engineering fee at the fine mesh is explicitly retained. -/
def terms (r : ℝ) (v : MS.Rake.Label B) (u : ℝ) (z : UVIndex) (w : R.family.label d) : ℝ :=
  (∑ q,∑ t,(((R.family.S.a z.1:ℂ)^v.h)⁻¹ * (Lobby.γ (basisR R) v) q *
      coefficient R d z.1 z.2 (RG17.atRef L d r z w) u t) *
    Wilson.moment (R.family.beta z.1 z.2) (fun U=>
      enrolled R v.h z.1 z.2 u q (site (R:=R) r z 0) U *
      enrolled R d z.1 z.2 u t (site (R:=R) r z 1) U)).re

theorem enrolled_pair (r : ℝ) (v : MS.Rake.Label B) {u : ℝ} (admitted : u≠0) (z : UVIndex) (w : R.family.label d) :
    row L d r v u z w = terms L d r v u z w := by
  unfold row terms
  rw [WilsonOrdinaryUltravioletPair.measured R v.h d z.1 z.2 _ _ admitted]
  simp only [coefficient,WilsonFactoryFiledGlyphs.paid R v z.1 z.2 u admitted]

variable (F) (J : ℝ→tower S)

local notation "E₀" => RG17.Free R.family d
local notation "b!" => WilsonOrdinaryHomogeneousDetectors.basis F d

/-- A genuine represented-pivot field chart on $F$, prior to any later
cutoff limit: the same real linear physical decoder takes the computed rows
of *every* independently filed glyph at *every* selected numeric cutoff,
and these are its exact original continuum reflected mixed readings.
All original second-slot charges are bought together, before source, torus,
and coupling, in the measured position chart. -/
theorem original (present : Pier.Lair.Present F J) (shift : L.shift=(fun _ _=>LinearEquiv.refl ..))
    (funds : Pier.Lair.Paying F (Pier.Lair.tender F L J) d) :
    ∃ (δ : ℝ), 0<δ ∧ ∃ (p : ℕ) (c : ℝ) (E : ℝ→(E₀→L[ℂ]R.family.label d)), 0≤c ∧
      ∀ᶠ r in trail, (∀ y,master L d r (E r y)=J r d y) ∧
        ‖E r‖≤c*R.family.path.levels.clock.hatBeta (L.level r)^p ∧
        ∃ X : (Handle F d→ℝ)→ₗ[ℝ]S.Field d,
          ∀ {B : Deck G} (v : MS.Rake.Label B) (u : ℝ), u≠0 → ∀ z : UVIndex,
            let right := fun i=>E r (adjoint R d (b! i))
            let k := fun i=>row L d r v u z (right i)
            (∀ i,mixed F J d r r ((J r d).symm (X k)) (b! i)=terms L d r v u z (right i)) ∧
            (∀ M : ℝ,(∀ i,|terms L d r v u z (right i)|≤M) →
              δ*‖(J r d).symm (X k)‖≤M*tariff F d) ∧
            (∀ x,(∀ i,mixed F J d r r ((J r d).symm x) (b! i)=terms L d r v u z (right i)) → x=X k) := by
  obtain ⟨δ,hδ,hX⟩ := finite_rows F d J present
  obtain ⟨p,c,E,hc,hE⟩ := WilsonMacroscopicMatchedSection.purchased F L J shift d funds
  refine ⟨δ,hδ,p,c,E,hc,?_⟩
  filter_upwards [hE,hX] with r hr hx
  obtain ⟨X,read,bill,only⟩ := hx
  refine ⟨hr.1,hr.2,X,?_⟩
  intro B v u hu z
  let w (i : Handle F d) := E r (adjoint R d (b! i))
  let k (i : Handle F d) := row L d r v u z (w i)
  have same (i : Handle F d) : k i=terms L d r v u z (w i) := enrolled_pair L d r v hu z (w i)
  refine ⟨fun i=>(read k i).trans (same i),fun M funded=>(bill k).trans (numerical F d k M fun i=>(same i).symm ▸ funded i),?_⟩
  intro x measured
  exact only k x fun i=>(measured i).trans (same i).symm

end YM.Integration.WilsonOrdinaryFiledPivot
