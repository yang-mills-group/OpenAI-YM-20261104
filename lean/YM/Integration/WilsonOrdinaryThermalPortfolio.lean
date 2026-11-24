import YM.Integration.WilsonOrdinaryThermalSource

/-! Every signed announced field fee through independently prescribed finite
orders is sampled at the actual positive-coupling torus, at its own
engineering height. One fixed calendar and its actual entire histories
realize the joint compact separated correlation on the original phase. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryThermalPortfolio
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

abbrev Term (i : Fin n) := Fin (k i+1) × Glyph B (p i).h

def row (i : Fin n) (a : Term p k i) : R.family.label a.2.size :=
  PowerSeries.coeff a.1.val (bore p Q (b i) i a.2) • Lobby.γ (basisR R) (owner a.2)

def fine (i : Fin n) (a : Term p k i) (z : UVIndex) : R.family.label a.2.size :=
  (((RG17.Report.coupling (fun j=>R.family.path.β z.1 z.2 j) (L.level r))^a.1.val : ℝ):ℂ) •
    WilsonOrdinaryThermalSource.cut L a.2.size (p i).h r (row (R:=R) Q p k b i a) z

def course (i : Fin n) (a : Term p k i) : S.Field a.2.size :=
  (((RG17.Report.coupling M.beta (L.level r))^a.1.val : ℝ):ℂ) •
    WilsonOrdinaryThermalSource.primary L a.2.size M (p i).h r (row (R:=R) Q p k b i a)

def leg (i : Fin n) (a : Term p k i) : S.Field (p i).h :=
  F.sector.derivatives.rise (Nat.le_of_lt_succ a.2.1.isLt) (course L M Q p k b r i a)

def field (i : Fin n) : S.Field (p i).h :=
  ∑ a : Term p k i,leg L M Q p k b r i a

def read (z : UVIndex) (x : Positions n) (t : (i : Fin n)→Term p k i) : ℂ :=
  R.family.ensemble (N:=z.1) (p:=z.2) (fun i=>(t i).2.size) (wrap _ ∘ x)
    (fun i=>fine L Q p k b r i (t i) z)

theorem single (hG : G.Simple) (t : (i : Fin n)→Term p k i)
    (admit : ∀ i,R.family.ref (t i).2.size≤L.level r)
    (K : Set (Points n)) (hk : IsCompact K) (separated : K⊆conf n) (ε : ℝ) (positive : 0<ε) :
    ∀ᶠ z in (M.cuts:Filter UVIndex),∀ x : Positions n,tag (R.family.S.a z.1) x∈K→
      dist (read L Q p k b r z x t)
        (S.classMoment S (fun i=>(p i).h) (tag (R.family.S.a z.1) x) (fun i=>leg L M Q p k b r i (t i))) < ε := by
  let m := L.level r
  let g := RG17.Report.coupling M.beta m
  let e (i : Fin n) := (t i).2.size
  let w (i : Fin n) := row (R:=R) Q p k b i (t i)
  let v (i : Fin n) := WilsonOrdinaryReportDeposit.input L (e i) (p i).h r (RG17.Report.thresholdFactor R.family M.beta m) (w i)
  let c (i : Fin n) := ((g^(t i).1.val : ℝ):ℂ) • RG17.locatedRef L (e i) r (v i)
  have bpos : 0<M.beta m := (div_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed m)) (by norm_num : (0:ℝ)<2)).trans_le (M.band m).1
  have gs : Tendsto (fun z : UVIndex=>RG17.Report.coupling (fun j=> R.family.path.β z.1 z.2 j) m) (M.cuts:Filter UVIndex) (𝓝 g) :=
    (Real.continuous_sqrt.continuousAt.tendsto.comp (M.measured m)).inv₀ (Real.sqrt_pos.2 bpos).ne'
  have measured (i : Fin n) : Tendsto (fine L Q p k b r i (t i)) (M.cuts:Filter UVIndex) (𝓝 (c i)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp (gs.pow (t i).1.val)).smul
      (WilsonOrdinaryThermalSource.transported L (e i) M (p i).h r (w i) (admit i))
  have proj_eq (i : Fin n) : S.project (e i) (c i)=course L M Q p k b r i (t i) := by
    dsimp only [c,course]
    rw [map_smul,RG17.payRef,WilsonOrdinaryThermalSource.at_limit]
  have paid := WilsonMovingCalibratedFields.paid R hG F (M.prior.trans L.certified) e
    (fun z i=>fine L Q p k b r i (t i) z) c measured K hk separated ε positive
  filter_upwards [paid] with z ready x hx
  let X := tag (R.family.S.a z.1) x
  have legal := separated hx
  let V (i : Fin n) := course L M Q p k b r i (t i)
  have inc (i : Fin n) : e i≤(p i).h := Nat.le_of_lt_succ (t i).2.1.isLt
  have height : S.classMoment S (fun i=>(p i).h) X (fun i=>leg L M Q p k b r i (t i))=S.classMoment S e X V :=
    AllOrder.Leading.moment_inclusion F.room.kernel.laws.toSymmetric F.phase.transport.injection inc legal V
  have projection : S.classMoment S e X V=S.value e X c := by
    dsimp only [V];simp_rw [←proj_eq]
    exact S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) legal (fun j=>⟨e j,c j⟩)
  rw [height,projection]
  exact ready x hx

theorem rows (X : Points n) :
    S.classMoment S (fun i=>(p i).h) X (field L M Q p k b r) =
      ∑ t : (i : Fin n)→Term p k i,S.classMoment S (fun i=>(p i).h) X (fun i=>leg L M Q p k b r i (t i)) := by
  classical
  unfold field
  rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]

/-- The complete physical product of the finite source fee jets, with
the genuine g at each cutoff, not a bound on their unsigned powers. -/
theorem original (hG : G.Simple) (admit : ∀ i (a : Term p k i),R.family.ref a.2.size≤L.level r)
    (K : Set (Points n)) (hk : IsCompact K) (separated : K⊆conf n) (ε : ℝ) (positive : 0<ε) :
    ∀ᶠ z in (M.cuts:Filter UVIndex),∀ x : Positions n,tag (R.family.S.a z.1) x∈K→
      dist (∑ t : (i : Fin n)→Term p k i,read L Q p k b r z x t)
        (S.classMoment S (fun i=>(p i).h) (tag (R.family.S.a z.1) x) (field L M Q p k b r)) < ε := by
  classical
  let I := (i : Fin n)→Term p k i
  let δ := ε/((Fintype.card I : ℝ)+1)
  have hδ : 0<δ := div_pos positive (by positivity)
  have all : ∀ᶠ z in (M.cuts:Filter UVIndex),∀ t : I,∀ x : Positions n,tag (R.family.S.a z.1) x∈K→
    dist (read L Q p k b r z x t)
      (S.classMoment S (fun i=>(p i).h) (tag (R.family.S.a z.1) x) (fun i=>leg L M Q p k b r i (t i)))<δ :=
    Filter.eventually_all.mpr fun t=>single L M Q p k b r hG t (fun i=>admit i (t i)) K hk separated δ hδ
  filter_upwards [all] with z close x hx
  rw [rows,dist_eq_norm,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t : I, ‖read L Q p k b r z x t - S.classMoment S (fun i=>(p i).h) (tag (R.family.S.a z.1) x) (fun i=>leg L M Q p k b r i (t i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : I,δ := Finset.sum_le_sum fun t _=>by simpa only [dist_eq_norm] using (close t x hx).le
    _ = (Fintype.card I : ℝ)*δ := by simp
    _ < ((Fintype.card I : ℝ)+1)*δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := by dsimp only [δ];field_simp

end YM.Integration.WilsonOrdinaryThermalPortfolio
