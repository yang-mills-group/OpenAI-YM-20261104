import YM.Integration.WilsonOrdinaryRelativeTariff

/-! Deposit the prescribed field on the actual reporting primary before
choosing any finer cutoff. The genuine fine source is supplied by atRef
and its complete historical Wilson trajectory is left intact. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryReportDeposit
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
variable {W : Type} (Q : MS.Land.Prescription B) (y : ℝ) (p : W→MS.Rake.Label B)

/-- Finite bound for all authentic normalized elementary grades at height d. -/
def slots (F : Labels.Frame G d) : ℕ := ∑j,(F.grades j).2

private theorem graded_bill (F : Labels.Frame G d) (t : ℝ) (raised : 1≤t) (w : F.Coeff) :
    F.coeffSize (F.scaled t w) ≤ t^slots d F*F.coeffSize w := by
  classical
  unfold Labels.Frame.coeffSize
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have degree : (F.grades j).2 ≤ slots d F :=
    Finset.single_le_sum (fun j _=>Nat.zero_le (F.grades j).2) (Finset.mem_univ j)
  rw [Labels.Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans raised) _)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ raised degree) (norm_nonneg _)

/-- The common observation-height fee and original angular normalizer are
written at the reporting date, in the original layout. -/
def input (H : ℕ) (r t : ℝ) (w : R.family.label d) : R.family.label d :=
  (((r / R.family.S.a (L.level r))^H : ℝ):ℂ) • (L.shift d r).symm ((R.family.labels.level d).scaled t w)

theorem shifted (H : ℕ) (r t : ℝ) (w : R.family.label d) :
    L.shift d r (input L d H r t w)=
    (((r / R.family.S.a (L.level r))^H : ℝ):ℂ) • ((R.family.labels.level d).scaled t w) := by
  rw [input,map_smul,LinearEquiv.apply_symm_apply]

theorem reserve (H : ℕ) (r t : ℝ) (hr : 0≤r) (ht : 1≤t) (w : R.family.label d) :
    RG12.mass R.family d (L.shift d r (input L d H r t w)) ≤
      (r/R.family.S.a (L.level r))^H * t^(slots d (R.family.labels.level d)) * RG12.mass R.family d w := by
  rw [shifted]
  let f : ℝ := (r / R.family.S.a (L.level r))^H
  have h : 0≤f := pow_nonneg (div_nonneg hr (R.family.S.a_pos _).le) _
  have bill : RG12.mass R.family d ((f:ℂ) • ((R.family.labels.level d).scaled t w)) =
      f*RG12.mass R.family d ((R.family.labels.level d).scaled t w) := by
    simp only [RG12.mass,Labels.Frame.coeffSize,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg h,Finset.mul_sum]
  change RG12.mass R.family d ((f:ℂ) • _) ≤ f*_*_
  rw [bill,mul_assoc]
  exact mul_le_mul_of_nonneg_left (graded_bill d (R.family.labels.level d) t ht w) h

/-- Actual original upper field, purchased before the cutoff, restores the
specified primary exactly at the reporting date. -/
theorem returned (H : ℕ) (r t : ℝ) (z : UVIndex) (w : R.family.label d)
    (admit : R.family.ref d≤L.level r) (deep : L.level r ≤ z.1) :
    let T := R.family.factory d z.1 z.2
    (T.entries (L.level r) (T.terminal.symm (RG17.atRef L d r z (input L d H r t w)))).x=
      ((R.family.S.a (L.level r)^d : ℝ):ℂ) • (((r/R.family.S.a (L.level r))^H : ℝ):ℂ) • ((R.family.labels.level d).scaled t w) := by
  let T := R.family.factory d z.1 z.2
  let A := RG12.charts R.family F.room.cutoff d (L.level r) z
  let v := input L d H r t w
  have native : A (RG17.atRef L d r z v) =
      (T.entries (L.level r) (T.terminal.symm (RG17.atRef L d r z v))).x := by
    unfold A
    rw [RG12.charts,dif_pos ⟨admit,deep⟩]; rfl
  change (T.entries _ (T.terminal.symm (RG17.atRef L d r z v))).x=_
  rw [←native,RG17.atRef,map_smul]
  change ((R.family.S.a (L.level r)^d : ℝ):ℂ) • A (A.symm (L.shift d r v))=_
  rw [LinearEquiv.apply_symm_apply,shifted]

/-- Ratio at the genuine original running temperature, without a bound or
an auxiliary coupling convention. -/
theorem thermostat (m : ℕ) :
    (R.family.path.levels.clock.hatCoupling m/R.family.path.levels.clock.threshold m)⁻¹=R.family.path.levels.clock.monitor m := by
  let S := R.family.path.levels.clock
  have gpos : 0<S.hatCoupling m := inv_pos.mpr (Real.sqrt_pos.2 (zero_lt_one.trans (R.family.path.levels.fits.delayed m)))
  have mpos : 0<S.monitor m := Real.exp_pos _
  change (S.hatCoupling m/(S.hatCoupling m*S.monitor m))⁻¹=S.monitor m
  field_simp

/-- Every independently commissioned coefficient at its own glyph height,
including its signed complex weight. The common spatial power is that of
the requested slot, after the genuine dimension compensation. -/
def mode (i : W) (n : ℕ) (r : ℝ) (v : Glyph B (p i).h) : R.family.label v.size :=
  input L v.size (p i).h r (R.family.path.levels.clock.monitor (L.level r))
    (PowerSeries.coeff n (bore p Q y i v) • Lobby.γ (basisR R) (owner v))

theorem filed (i : W) (n : ℕ) (r : ℝ) (v : Glyph B (p i).h) (z : UVIndex)
    (admit : R.family.ref v.size≤L.level r) (deep : L.level r≤z.1) :
    let T := R.family.factory v.size z.1 z.2
    let m := L.level r
    let g := R.family.path.levels.clock.hatCoupling m
    let θ := R.family.path.levels.clock.threshold m
    (T.entries m (T.terminal.symm (RG17.atRef L v.size r z (mode L Q y p i n r v)))).x=
      ((R.family.S.a m^v.size : ℝ):ℂ) • (((r/R.family.S.a m)^(p i).h : ℝ):ℂ) •
      (R.family.labels.level v.size).scaled (g/θ)⁻¹
        (PowerSeries.coeff n (bore p Q y i v) • Lobby.γ (basisR R) (owner v)) := by
  dsimp only
  rw [thermostat]
  exact returned L v.size (p i).h r _ z _ admit deep

end YM.Integration.WilsonOrdinaryReportDeposit
