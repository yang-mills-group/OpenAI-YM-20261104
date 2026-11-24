import YM.Integration.WilsonPhysicalCommonElection
import YM.Integration.WilsonPhysicalDeterminingTree
import YM.Integration.WilsonViewerEarnedGrid

/-! Correlations in every viewer and ordinary finite trees on one originally selected
hierarchy. A finite family may include all proper faces of a joint experiment. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalCorrelationAndOrdinaryOPE
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato Lattice
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonThermometerWeakMeasuredSeries WilsonPositionHomogeneousFrame
open WilsonViewerGridPins WilsonViewerReportingGrid WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonLimitConstruction
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {L:EveryPhase.Almanac F} {Y:(Bel R.family.book).Hierarchy}
    {arch:Trace.Terrace.Arch R.family} {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop} (run:Selected.{u} F L Q J Y arch ℓ simple cohort)
variable (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "pub" => homogeneous F J Z

/-- All occupied subsets, determining rows and targets can be entered at once, in
different arities. The conclusion has a single opening in the physical radius. -/
def Schwinger {σ : Prescription (Press.portDeck G)} {dial : Bool}
    (matched : Main.Match Z simple M σ dial) : Prop :=
  ∀ H, ∃ P : Report F ℓ H θ, ∀ (l : ℕ) (n : Fin l → ℕ) (d : (a : Fin l) → Caps (n a))
    (v : (a : Fin l) → MaxwellSlots R.family (d a)) (within : ∀ a i, d a i ≤ H)
    (W : Fin l → Finset E4) (j p q : Fin l → ℕ),
    (∀ a, WilsonThermometerWeakSignedJets.high (j a) (p a) ≤ q a) →
    (∀ a, PinBill Z M matched ν (v a) (within a) P (W a)
      (WilsonThermometerWeakSignedJets.high (j a) (p a)+1) (q a)) →
    ∀ K : (a : Fin l) → Set (Points (n a)), (∀ a, IsCompact (K a)) →
    (∀ a, K a ⊆ conf (n a)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail,
    ∀ a, ∀ x ∈ K a, ∀ viewer : Viewers F,
      ‖iteratedFDeriv ℝ (j a) (measured F viewer (pub r) (v a) r) x -
        iteratedFDeriv ℝ (j a)
          (approximate (coefficient Z M ν H (commonCaps (v a) (within a))) (p a) (θ r)) x‖ ≤ ε*(θ r)^(p a)

variable {T : Campaign R} {pillar : Campaign.Pillars R T} {a₀ : Axis} {κ : ℝ}
    {s : WilsonOriginalAllOrderCourse.Schedule G}

def Conclusion (dial : Bool) : Prop :=
    ∃ σ, ∃ matched : Main.Match Z simple M σ dial, Coupling G θ ∧ LogTrace F Q.port ∧
      Schwinger (F:=F) (ℓ:=ℓ) (J:=J) Z M ν matched ∧
      ∀ (report : ℕ), 0 < report → ∀ {n : ℕ} (p : Fin n → Tree)
        (v : (fork n p).Leaf → S.Tag) (D : (fork n p).Inner → ℕ) (H : ℕ)
        {I : Type} [Fintype I] (ex : I → S.Tag) {U η ε δ : ℝ},
        0 ≤ U → ∀ ηp : 0 < η, 0 < ε → 0 < δ →
        WilsonPhysicalDeterminingTree.Outcome run Z M ν report p v D H ex U η ε δ ηp

/-- The archive pays the genuine FVA prior, running pace and original reflection/hearing
facilities. The regulator and field prescription are shared by the entire conclusion. -/
theorem original (cash : WilsonOriginalAllOrderCourse.Paid.{u} a₀ simple κ s R T pillar)
    (dial : Bool)
    (rose : ℝ → Group R.family 6) (book : Book (f:=f) (l:=ℓ) (H:=Y) rose J)
    {B : ℕ} (hB : 0 < B) (fine index : ℝ → ℕ)
    (schedule : WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index)
    {m : ℕ} (d₀ : ℕ) (φ : Test m) (v₀ : Fin m → Sec G d₀)
    (first : WilsonMaxwellThermometerKineticRequest.earned (Y:=ℓ) Z F J rose simple
      (B:=B) fine index d₀ φ v₀ 1) :
    Conclusion run Z M ν dial := by
  obtain ⟨fund,pace,_⟩ := WilsonPhysicalCommonElection.finances cash
  obtain ⟨σ,matched⟩ := Main.wilson_to_MS Z simple M dial
  obtain ⟨clock,rows⟩ := run.earned_grid Z M matched rose book hB pace fine index schedule ν d₀ φ v₀ first
  unfold Conclusion
  refine ⟨σ,matched,clock,?_,?_,?_⟩
  · exact OPE.tickets_suffice F run.facilities run.bliss.lies run.matrix Q.spans
  · intro H
    obtain ⟨P,corr⟩ := rows H
    refine ⟨P,?_⟩
    intro l n d v within W j p q retain paid K compact clear ε ep
    exact eventually_all.mpr fun a =>
      corr (n a) (d a) (v a) (within a) (W a) (j a) (p a) (q a) (retain a) (paid a)
        (K a) (compact a) (clear a) ε ep
  · intro report live n p v D H I _ ex U η ε δ u0 ηp εp δp
    exact WilsonPhysicalDeterminingTree.on_scheme run Z M ν matched fund pace Z.store report live clock
      p v D H ex u0 ηp εp δp

end YM.Integration.WilsonPhysicalCorrelationAndOrdinaryOPE
