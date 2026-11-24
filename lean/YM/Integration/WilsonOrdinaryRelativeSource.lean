import YM.Integration.WilsonOrdinaryCountertermField
import YM.Integration.WilsonPhysicalExteriorCoherentGrades
import YM.Integration.WilsonPhysicalExteriorMeasuredTariff

/-! Compensation of the two original fee clocks on the *actual* signed
microscopic source. All strictly lower engineering rows vanish before
sampling the true Wilson measure. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryRelativeSource
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
open WilsonPhysicalExteriorFeeShift WilsonPhysicalExteriorRunningRows
open WilsonPhysicalExteriorMeasuredTariff
open WilsonOrdinaryPricedGlyph
open Precision
variable (R) {W : Type} {O : Booked B} (Q : MS.Land.Prescription B)
variable (a b : ℝ) (h : ℕ) (z : UVIndex) (u : ℝ) (x : Site (R.family.side z.1 z.2))
variable (U : Config G (R.family.side z.1 z.2))

/-- Original earlier-clock fee row with the original bulk reparametrization,
applied to the entire same set of actual microscopic signed field symbols.
Here the deposited positive-cutoff material is fixed when repricing the fees. -/
def previous (s : Glyph B h) : PowerSeries ℂ :=
  ∑ v : Glyph B h, reprice Q.team a b (WilsonPhysicalExteriorFeeShift.frame Q h a s v) *
    PowerSeries.C (material R (owner v) z.1 z.2 u x U)

private theorem top_sum (M : MS_Data G O) (hG : G.Simple)
    (paid : TaylorOKPl M (Lobby.Table (basisR R) B) Q) (w : Plaid B h)
    (f : Glyph B h→PowerSeries ℂ) :
    (∑ s ∈ Finset.univ.filter (fun s : Glyph B h=>s.size=h),
       coordinates Q h b a b (Land.read w) s * f s)=
    ∑ s : Glyph B h,coordinates Q h b a b (Land.read w) s * f s := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s _ hs
  have ne : s.size≠h := fun e=>hs (Finset.mem_filter.mpr ⟨mem_univ _,e⟩)
  have lower : s.size<h := lt_of_le_of_ne (Nat.le_of_lt_succ s.1.isLt) ne
  rw [WilsonPhysicalExteriorCoherentGrades.original R M Q hG paid h w s lower a b,zero_mul]

/-- The actual charged field coefficient, from the independent MS prescription
at time b, equals the finite same-engineering-height sum of the genuinely
earlier repriced field coordinates, for every regulator/configuration. -/
theorem physical (M : MS_Data G O) (hG : G.Simple)
    (paid : TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (p : W→MS.Rake.Label B) (i : W) (k : ℕ) (ε : ℝ) (admit : ε≠0) (coupled : u≠0) :
    WilsonOrdinaryPricedGlyph.field R Q b p ε i k z u x U = ((ε:ℂ)^(p i).h)⁻¹ *
      coeff k (∑ s ∈ Finset.univ.filter (fun s : Glyph B (p i).h=>s.size=(p i).h),
        coordinates Q (p i).h b a b (Land.read (p i).item) s *
        previous R Q a b (p i).h z u x U s) := by
  classical
  let H := (p i).h
  let φ := (reprice Q.team a b).toRingHom
  have old : oldFrame Q H a*WilsonPhysicalExteriorFeeShift.frame Q H a=1 := by
    rw [oldFrame,WilsonPhysicalExteriorFeeShift.frame,←map_mul,
      Matrix.nonsing_inv_mul _ (MSFeeCoordinates.determinant Q H),map_one]
  have both : coordinates Q H b a b * φ.mapMatrix (WilsonPhysicalExteriorFeeShift.frame Q H a)=
      WilsonPhysicalExteriorFeeShift.frame Q H b := by
    change (WilsonPhysicalExteriorFeeShift.frame Q H b*φ.mapMatrix (oldFrame Q H a))*φ.mapMatrix
      (WilsonPhysicalExteriorFeeShift.frame Q H a)=_
    rw [Matrix.mul_assoc,←map_mul,old,map_one,Matrix.mul_one]
  have column (v : Glyph B H) : (∑ s : Glyph B H,coordinates Q H b a b (Land.read (p i).item) s *
      reprice Q.team a b (WilsonPhysicalExteriorFeeShift.frame Q H a s v))=bore p Q b i v :=
    (congrFun (congrFun both (Land.read (p i).item)) v).trans (WilsonPhysicalExteriorFeeShift.padded Q b (Land.read (p i).item) v)
  have lift : (∑s : Glyph B H,coordinates Q H b a b (Land.read (p i).item) s * previous R Q a b H z u x U s) =
      ∑ v : Glyph B H,bore p Q b i v * PowerSeries.C (material R (owner v) z.1 z.2 u x U) := by
    simp only [previous,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [←column,Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _=>(mul_assoc _ _ _).symm
  rw [WilsonOrdinaryPricedGlyph.dimensional (R:=R) (Q:=Q) (y:=b) (p:=p) (ε:=ε) (i:=i) (k:=k) (z:=z) coupled admit]
  rw [top_sum R Q a b H M hG paid (p i).item,lift,map_sum]
  simp only [PowerSeries.coeff_mul_C]
  congr 1

/-- Numerical convolution at each perturbative order inside the honest
Wilson cutoff, after the strictly lower engineering rows have been removed. -/
theorem convolution (M : MS_Data G O) (hG : G.Simple)
    (paid : TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (p : W→MS.Rake.Label B) (i : W) (k : ℕ) (ε : ℝ) (admit : ε≠0) (coupled : u≠0) :
    WilsonOrdinaryPricedGlyph.field R Q b p ε i k z u x U = ((ε:ℂ)^(p i).h)⁻¹ *
      ∑s ∈ Finset.univ.filter (fun s : Glyph B (p i).h=>s.size=(p i).h),
      ∑j ∈ Finset.HasAntidiagonal.antidiagonal k, coeff j.1 (coordinates Q (p i).h b a b (Land.read (p i).item) s) *
        coeff j.2 (previous R Q a b (p i).h z u x U s) := by
  rw [physical R Q a b z u x U M hG paid p i k ε admit coupled,map_sum]
  simp only [PowerSeries.coeff_mul]

end YM.Integration.WilsonOrdinaryRelativeSource
