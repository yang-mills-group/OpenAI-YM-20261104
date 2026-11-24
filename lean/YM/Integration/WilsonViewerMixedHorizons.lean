import YM.Integration.WilsonViewerCommonPrescription

/-! A physical input remains at its own horizon. Raising all sources to the
same finite cap for the signed independent read gives exactly the same
separated test in every original viewer. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score
open MS MS.Land MS.Fleet WilsonPositionHomogeneousFrame WilsonPositionSeparatedProfileMatching
open scoped Topology BigOperators Classical

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin} {J : ℝ → PhysMS.tower S}
    {Y : (Bel R.family.book).Hierarchy} {A : Trace.Terrace.Arch R.family}
    {ℓ : Ultrafilter (ℕ × ℕ)} {cohort : Ultrafilter (ℕ × ℕ) → Prop} {simple : G.Simple}
    (run : Selected.{u} F L Q J Y A ℓ simple cohort) (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    {branch : Bool} (matchMS : Main.Match Z simple M σ branch)
local notation "P" => homogeneous F J Z
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z

include run matchMS in
theorem Selected.raised {k H : ℕ} (h : k ≤ H) :
    ∀ᶠ r in trail, ∀ x : RG17.Free R.family k,
      P r H ((Maxwell.Free.scheme R.family.labels).rise h x) =
        F.sector.derivatives.rise h (P r k x) := by
  induction h with
  | refl =>
    exact Eventually.of_forall fun r x => by
      rw [(Maxwell.Free.scheme R.family.labels).arrival (Maxwell.table_sym _) (Maxwell.Free.scheme_filters _),
        F.sector.derivatives.arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection]
  | @step H h smaller =>
    have nextDate := WilsonPositionHomogeneousFrame.adjacent F J Z run.leading run.obeys simple
      (WilsonPositionHomogeneousCoefficients.purchased Z matchMS) H
    filter_upwards [smaller,nextDate] with r carried next x
    rw [← (Maxwell.Free.scheme R.family.labels).transit (Maxwell.table_sym _) (Maxwell.Free.scheme_filters _)
      h (Nat.le_succ H), next, carried,
      F.sector.derivatives.transit F.room.kernel.laws.toSymmetric F.phase.transport.injection]

variable {n : ℕ} {d : Caps n} (v : MaxwellSlots R.family d) {H : ℕ} (within : ∀ i, d i ≤ H)
def commonCaps : Fin n → Sec G H := fun i =>
  (Maxwell.Free.fields R.family.labels H) ((Maxwell.Free.scheme R.family.labels).rise (within i) (v i))

include run matchMS in
theorem Selected.same_caps (φ : Test n) :
    ∀ᶠ r in trail, ∀ p : Viewers F,
      WilsonPositionPhaseProfileTest.reading F J Z p φ v r =
        observed Z F J p H φ (commonCaps v within) r := by
  have compatible := eventually_all.mpr fun i => run.raised Z M matchMS (within i)
  filter_upwards [compatible,RG17.positiveLength] with r atR rp p
  apply φ.apply_eq
  intro x hx
  unfold PhysMS.measured
  simp only [commonCaps,LinearEquiv.symm_apply_apply,atR]
  exact (AllOrder.Leading.moment_inclusion (spectate F p).laws.toSymmetric (spectate_ready F p)
    within (Work.A05.smul_conf rp hx) (fun i => P r (d i) (v i))).symm

include run matchMS in
theorem Selected.mixed {ν : ℝ} (φ : Test n) (q : ℕ) (g : ℝ → ℝ) (coupling : Coupling G g)
    (clock : ∃ B : ℝ, 0 < B ∧ ∀ᶠ r in trail, g r ≤ B * |θ r|)
    (signed : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail,
      ‖WilsonPositionPhaseProfileTest.reading F J Z none φ v r -
        polynomial Z M ν H φ (commonCaps v within) q (θ r)‖ ≤ ε*|θ r|^q) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail, ∀ p : Viewers F,
      ‖WilsonPositionPhaseProfileTest.reading F J Z p φ v r -
        polynomial Z M ν H φ (commonCaps v within) q (θ r)‖ ≤ ε*|θ r|^q := by
  have fields := run.same_caps Z M matchMS v within φ
  have corr := run.correlations Z M ν H φ (commonCaps v within) q g coupling clock
    (fun ε ep => by filter_upwards [fields,signed ε ep] with r visit price
                    rwa [←visit none])
  intro ε ep
  filter_upwards [fields,corr ε ep] with r visit estimate p
  rw [visit p]
  exact estimate p

end YM.Integration.WilsonViewerElectedHierarchy
end
