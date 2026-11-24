import YM.Integration.WilsonViewerPositionSeries

/-! Raising each actual input to a common finite cap inside the signed test
preserves its separated position jets at every viewer. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score MS MS.Land MS.Fleet
open WilsonPositionHomogeneousFrame WilsonThermometerWeakMeasuredSeries
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    {branch : Bool} (ms : Main.Match Z simple M σ branch) (ν : ℝ) {n H : ℕ} {d : Caps n}
    (v : MaxwellSlots R.family d) (within : ∀ i, d i≤H)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "pub" => homogeneous F J Z
local notation "c" => coefficient Z M ν H (commonCaps v within)

include run ms in
theorem Selected.common_positions : ∀ᶠ r in trail, ∀ viewer : Viewers F,
    EqOn (measured F viewer (pub r) v r)
      (measured F viewer (pub r) (directions R H (commonCaps v within)) r) (conf n) := by
  filter_upwards [eventually_all.mpr fun i => run.raised Z M ms (within i),RG17.positiveLength]
    with r raised rp viewer x hx
  unfold PhysMS.measured
  simp only [directions,commonCaps,LinearEquiv.symm_apply_apply,raised]
  exact (AllOrder.Leading.moment_inclusion (spectate F viewer).laws.toSymmetric (spectate_ready F viewer)
    within (Work.A05.smul_conf rp hx) (fun i => pub r (d i) (v i))).symm

include run ms in
theorem Selected.mixed_positions (j p D q : ℕ) (retains : WilsonThermometerWeakSignedJets.high j p ≤ q)
    (temperature : Coupling G θ) (legal : ∀ a≤q, ContDiffOn ℝ ∞ (c a) (conf n))
    (signed : WilsonThermometerWeakValueRecovery.Signed trail (conf n)
      (fun r => measured F none (pub r) v r - approximate c q (θ r))
      θ (WilsonThermometerWeakSignedJets.high j p+1) D) :
    ∀ K, IsCompact K → K ⊆ conf n → ∀ ε : ℝ, 0<ε → ∀ᶠ r in trail, ∀ x∈K, ∀ viewer : Viewers F,
      ‖iteratedFDeriv ℝ j (measured F viewer (pub r) v r) x -
        iteratedFDeriv ℝ j (approximate c p (θ r)) x‖ ≤ ε*(θ r)^p := by
  have same := run.common_positions Z M ms v within
  have comparison := run.position Z M ν H (commonCaps v within) j p D q retains temperature legal
  have paid : WilsonThermometerWeakValueRecovery.Signed trail (conf n)
      (fun r => measured F none (pub r) (directions R H (commonCaps v within)) r -
        approximate c q (θ r)) θ (WilsonThermometerWeakSignedJets.high j p+1) D := by
    intro K compact clear
    obtain ⟨A,An,first⟩ := signed K compact clear
    refine ⟨A,An,?_⟩
    filter_upwards [same,first] with r atR invoice φ support w wp tariff
    have holds := invoice φ support w wp tariff
    apply Eq.trans_le _ holds
    apply congrArg norm
    apply φ.apply_eq
    intro x hx
    exact congrArg (fun value => value - approximate c q (θ r) x) (atR none hx).symm
  intro K compact clear ε ep
  filter_upwards [same,comparison paid K compact clear ε ep] with r atR result x hx viewer
  have eq : measured F viewer (pub r) v r =ᶠ[𝓝 x]
      measured F viewer (pub r) (directions R H (commonCaps v within)) r := by
    filter_upwards [(conf_open n).mem_nhds (clear hx)] with y hy using atR viewer hy
  rw [(eq.iteratedFDeriv ℝ j).eq_of_nhds]
  exact result x hx viewer

end YM.Integration.WilsonViewerElectedHierarchy
end
