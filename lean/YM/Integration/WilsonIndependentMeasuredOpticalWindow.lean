import YM.Integration.WilsonIndependentMeasuredOpticalClock
import YM.Integration.WilsonOriginalTwoFlatPublicMixedSpan

/-! The named physical starting date in the same licensed finite epoch.
The lower reporter is selected before the source, cutoff and period. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
namespace YM.Integration.WilsonIndependentMeasuredOpticalWindow
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open WilsonPositionProgramTrialOpticalBand (Band)
structure Slot (R:Run G) (V:XSpace.Run) (f K i:ℕ) : Prop where
  spacing : R.family.S.a K/R.family.S.a f=(V.step i).spacing
  gross : R.family.path.levels.clock.hatBeta f  ≤  (V.den i:ℝ)
  restored : R.family.path.levels.clock.hatBeta K  ≤  (1+G.slopeConstant)*(V.den i:ℝ)

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (V:XSpace.Run){axis:Axis}{ε:ℝ}(price:WilsonPositionProgramArithmetic.course simple axis ε R.kit)
    {d₀:ℕ}(hd:0<d₀)(ratio:V.ratio=(3:ℕ)^d₀)(stage τ:ℕ)(grown:2 ≤ τ)
    (D T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∃B:Band R V (berth R τ) stage,∀cutoff:ℕ,∀ᶠr in trail,
      ∀ρ:I→{s:ℝ // 0<s ∧ s<δ}, (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      let i:=B.mesh (f-B.reporter)
      B.reporter ≤ f ∧ cutoff ≤ i ∧ a f ≤ r ∧ Slot R V f (berth R τ f) i ∧
        ∀v,(ρ v).val/a f  ≤  (V.den i:ℝ)^(2*T+11+2*h) := by
  have charge:=WilsonPositionProgramTrialOpticalBand.bracket R simple slow grown
  obtain ⟨B⟩:=WilsonPositionProgramTrialOpticalBand.elected R simple V price hd ratio stage (berth R τ) (by positivity) charge
  refine ⟨B,?_⟩
  intro cutoff
  have heat:=WilsonIndependentMeasuredOpticalClock.original R simple V B charge
  obtain ⟨start,late⟩:=eventually_atTop.1 (heat.and (B.cofinal.eventually_ge_atTop cutoff))
  have stop : ∀ᶠr in trail,r<R.family.S.a (B.reporter+start) :=
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (R.family.S.a_pos _))
  filter_upwards [stop,WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books] with r small physical
  intro ρ span near m f i
  obtain ⟨fine,homes⟩:=physical ρ span near
  change a f ≤ r at fine
  have located : B.reporter+start ≤ f := by
    by_contra! bad
    exact (not_le_of_gt (R.family.S.strictAnti bad)) (fine.trans small.le)
  have clear : B.reporter ≤ f := by omega
  have eqn : B.reporter+(f-B.reporter)=f := Nat.add_sub_of_le clear
  have paid:=late (f-B.reporter) (by omega)
  dsimp only at paid
  rw [eqn] at paid
  have entry:=B.spacing (f-B.reporter)
  rw [eqn] at entry
  exact ⟨clear,paid.2,fine,⟨entry,paid.1.1,paid.1.2⟩,fun v=>
    ((div_le_iff₀ (R.family.S.a_pos f)).2 (homes v).2).trans
      (pow_le_pow_left₀ ((zero_lt_one.trans ((P).fits.delayed f)).le) paid.1.1 _)⟩

end YM.Integration.WilsonIndependentMeasuredOpticalWindow
