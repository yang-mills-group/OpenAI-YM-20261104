import YM.Integration.WilsonOrdinaryThermalPortfolio

/-! One normalized, fully signed positive-measure physical experiment,
with all marks' genuine finite thermal polynomial fields in one product. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryThermalExperiment
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


open Cells Push.GridApprox FullVolume
open WilsonOrdinaryThermalSource
variable (M : Calendar L) (Q : MS.Land.Prescription B) {n : ℕ}
  (p : Fin n→MS.Rake.Label B) (k : Fin n→ℕ) (b : Fin n→ℝ) (r : ℝ)

open WilsonOrdinaryThermalPortfolio

def factor (z : UVIndex) (x : Positions n) (i : Fin n) (U : Config G (R.family.side z.1 z.2)) : ℂ :=
  ∑ a : Term p k i,R.family.O z.1 z.2 (d:=a.2.size) (fine L Q p k b r i a z) ((wrap _ ∘ x) i) U

def sample (z : UVIndex) (x : Positions n) : ℂ :=
  ∫ U, ∏ i,factor L Q p k b r z x i U ∂(Wilson.law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2))

theorem cash (z : UVIndex) (x : Positions n) :
    sample L Q p k b r z x = ∑ t : (i : Fin n)→Term p k i,read L Q p k b r z x t := by
  classical
  let I := (i : Fin n)→Term p k i
  let law₀ := Wilson.law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2)
  let ν (i : Fin n) (a : Term p k i) (U : Config G (R.family.side z.1 z.2)) :=
    R.family.O z.1 z.2 (d:=a.2.size) (fine L Q p k b r i a z) ((wrap _∘x) i) U
  have budget (t : I) : MeasureTheory.Integrable (fun U=>∏i,ν i (t i) U) law₀ :=
    R.family.integrableR (fun i=>⟨(t i).2.size,fine L Q p k b r i (t i) z⟩) (wrap _ ∘ x)
  change (∫ U,∏i,∑a : Term p k i,ν i a U ∂law₀) = ∑ t : I,∫ U,∏i,ν i (t i) U ∂law₀
  rw [←MeasureTheory.integral_finsetSum _ (fun t _=>budget t)]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U=>Fintype.prod_sum (fun i a=>ν i a U))

theorem original (hG : G.Simple) (admit : ∀ i (a : Term p k i),R.family.ref a.2.size≤L.level r)
    (K : Set (Points n)) (hk : IsCompact K) (separated : K⊆conf n) (ε : ℝ) (positive : 0<ε) :
    ∀ᶠ z in (M.cuts:Filter UVIndex),∀ x : Positions n,tag (R.family.S.a z.1) x∈K→
      dist (sample L Q p k b r z x)
        (S.classMoment S (fun i=>(p i).h) (tag (R.family.S.a z.1) x) (field L M Q p k b r))<ε := by
  simp_rw [cash]
  exact WilsonOrdinaryThermalPortfolio.original L M Q p k b r hG admit K hk separated ε positive

/-- The same finite physical observable restores the entire named coefficient
in its primary on the very same cut, including its thermal evaluation weight. -/
theorem primary (z : UVIndex) (i : Fin n) (a : Term p k i) (admit : R.family.ref a.2.size≤L.level r) (deep : L.level r≤z.1) :
    let d₀ := a.2.size
    let T := R.family.factory d₀ z.1 z.2
    let m := L.level r
    let g := RG17.Report.coupling (fun j=>R.family.path.β z.1 z.2 j) m
    (T.entries m (T.terminal.symm (fine L Q p k b r i a z))).x =
      ((R.family.S.a m^d₀:ℝ):ℂ) • (((r/R.family.S.a m)^(p i).h:ℝ):ℂ) •
        (R.family.labels.level d₀).scaled (RG17.Report.thresholdFactor R.family (fun j=>R.family.path.β z.1 z.2 j) m)
          (((g^a.1.val:ℝ):ℂ) • row (R:=R) Q p k b i a) := by
  let m := L.level r
  let g := RG17.Report.coupling (fun j=>R.family.path.β z.1 z.2 j) m
  let w := row (R:=R) Q p k b i a
  let h := a.2.size
  let scal : ℂ := ↑(g^a.1.val : ℝ)
  have linear : fine L Q p k b r i a z =
      WilsonOrdinaryThermalSource.cut L h (p i).h r (scal • w) z := by
    dsimp only [WilsonOrdinaryThermalPortfolio.fine,WilsonOrdinaryThermalSource.cut,RG17.Report.finiteColumn,RG17.Report.rescales]
    rw [map_smul,map_smul]
    change scal • (_ • (_ • _))=_ • (_ • (scal • _))
    simp only [smul_smul]
    congr 1;ring
  dsimp only
  rw [linear,WilsonOrdinaryThermalSource.at_cut]
  exact WilsonOrdinaryReportDeposit.returned L h (p i).h r _ z (scal • w) admit deep

end YM.Integration.WilsonOrdinaryThermalExperiment
