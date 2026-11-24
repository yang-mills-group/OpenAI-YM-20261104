import YM.Integration.WilsonOrdinaryRunRegistration
import YM.Integration.WilsonRichFirstCorrected

/-! The original prescribed field counterterms placed, with both phases,
on the measured Wilson cutoff. The microscopic engineering fees cancel
to the one prescribed charge before summing the independently weighted glyphs. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryPricedGlyph
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
variable (R) {W : Type}
variable (Q : MS.Land.Prescription B) (y : ℝ) (p : W→MS.Rake.Label B)
variable (ε : ℝ) (i : W) (k : ℕ) (z : UVIndex)

/-- Coefficient of the independently appointed field prescription, with the
true common observation unit a_N/ε and this glyph's own engineering height. -/
def amplitude (v : Glyph B (p i).h) : ℂ :=
  coeff k (changePrice Q y p ε i v) * (((R.family.S.a z.1:ℂ)/(ε:ℂ))^v.size)

/-- The full independent native field-fee coefficient, deposited as one
signed source on all real microscopic configurations before integration. -/
def field (u : ℝ) (x : Site (R.family.side z.1 z.2)) (U : Config G (R.family.side z.1 z.2)) : ℂ :=
  ∑ v : Glyph B (p i).h,amplitude R Q y p ε i k z v *
    R.family.O z.1 z.2 (ledger R (owner v) z.1 z.2 u) x U

/-- Removal of the two terminal coordinatizations and collapse of all
lower-grade engineering powers on the exact earned Wilson fields. -/
theorem dimensional {u : ℝ} (positive : u≠0) (admit : ε≠0) (x : Site (R.family.side z.1 z.2))
    (U : Config G (R.family.side z.1 z.2)) :
    field R Q y p ε i k z u x U=((ε:ℂ)^(p i).h)⁻¹ *
      ∑ v : Glyph B (p i).h,coeff k (bore p Q y i v) * material R (owner v) z.1 z.2 u x U := by
  classical
  have hε : (ε:ℂ)≠0 := Complex.ofReal_ne_zero.mpr admit
  have ha : (R.family.S.a z.1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (R.family.S.a_pos _).ne'
  unfold field amplitude
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [changePrice,PowerSeries.coeff_C_mul,WilsonFactoryFiledGlyphs.visible R (owner v) z.1 z.2 u positive]
  change ((ε:ℂ)^((v.size:ℤ)-(p i).h)*_)*(((R.family.S.a z.1:ℂ)/(ε:ℂ))^v.size)*(((R.family.S.a z.1:ℂ)^v.size)⁻¹*_) = _
  rw [zpow_sub₀ hε,zpow_natCast,zpow_natCast,div_pow]
  field_simp

/-- Under the unaltered positive law, this *single* signed deposited source
equals the complex-linear combination of the true independent native reads.
It may now be fed to the one common physical complex field decoder. -/
theorem measured (d : ℕ) (u : ℝ) (x t : Site (R.family.side z.1 z.2))
    (b : R.family.label d) :
    Wilson.moment (R.family.beta z.1 z.2) (fun U=>field R Q y p ε i k z u x U*R.family.O z.1 z.2 b t U)=
      ∑ v : Glyph B (p i).h, WilsonOrdinaryCutBilinear.integral R d (owner v).h z x t
        (amplitude R Q y p ε i k z v • ledger R (owner v) z.1 z.2 u) b := by
  classical
  let μ := Wilson.law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2)
  let a (v : Glyph B (p i).h) := ledger R (owner v) z.1 z.2 u
  let c (v : Glyph B (p i).h) := amplitude R Q y p ε i k z v
  let K (v : Glyph B (p i).h) := fun U=>R.family.O z.1 z.2 (c v • a v) x U*R.family.O z.1 z.2 b t U
  have live (v : Glyph B (p i).h) : Integrable (K v) μ := Wilson.continuous_integrable _
    ((R.family.continuousO _ _ _ _ _).mul (R.family.continuousO _ _ _ _ _))
  change (∫ U,field R Q y p ε i k z u x U*R.family.O z.1 z.2 b t U ∂μ) = ∑v, ∫ U,K v U ∂μ
  rw [←integral_finsetSum _ (fun v _=>live v)]
  apply integral_congr_ae
  filter_upwards [] with U
  unfold field
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg (fun q : ℂ=>q * R.family.O z.1 z.2 b t U)
    (congrFun ((R.family.linearO z.1 z.2 (owner v).h x).map_smul (c v) (a v)) U).symm

end YM.Integration.WilsonOrdinaryPricedGlyph
