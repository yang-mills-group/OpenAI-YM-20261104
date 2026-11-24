import YM.Integration.WilsonCapturedPrimaryWardTiling

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardFaces
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction Extra.Histories PhysicalNext.Repeat.Legato
open RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat Legato Bandage
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells
open XSpace XSpace.Rose Push.GridApprox OPE OPE.Orbits
open WilsonPositionThermometerCapStation WilsonOffsetReportingProducts WilsonOffsetEquationLaw
open WilsonAddressedEquationShelf WilsonCapturedPrimaryPhysicalArray
open private inside_sub from YM.Integration.WilsonCapturedPrimaryWardFile
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {n N p : ℕ}
variable (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
  (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) (b : Presentation R.family)

def projected (d : Fin n → ℕ) (x : (i : Fin n) → R.family.label (d i))
    (s : Finset (Fin n)) (o : Fin n → Site (R.family.side N p)) : Config G (R.family.side N p) → ℂ :=
  fun U => ∏ i ∈ s, R.family.O N p (b.step (d i) (N,p) (x i)) (o i) U

def adjusted (d : Fin n → ℕ) (x : (i : Fin n) → R.family.label (d i))
    (s : Finset (Fin n)) (o : Fin n → Site (R.family.side N p)) : Config G (R.family.side N p) → ℂ :=
  fun U => ∏ i ∈ s, (R.family.O N p (x i) (o i) U -
    residual R.family (V (d i)) N p (P (d i) (N,p))
      (x i-b.step (d i) (N,p) (x i)) (o i) U)

variable (portfolio : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
  (issued : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a))
include W portfolio issued in
/-- All subwords use the same Wilson configurations, degree choices and microscopic cell. -/
theorem original (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v J h : ℕ) (wide : 4 < v) (d : Fin n → ℕ) (φ : Test n) :
    ∀ᶠ r : ℝ in 𝓝[>]0, let k := WilsonMeasuredWindow.stop R.family.path.levels simple v r
    ∀ N p (_live : k ≤ N) (tiled : J ≤ N) (z : Fin n → Site (R.family.side N p)),
    WilsonCenteredCompactBooking.mass R φ r (N,p) z ≠ 0 →
    ∀ (axis : Option (Fin n)) (s : Finset (Fin n)) (x : (i : Fin n) → R.family.label (d i))
      (c : R.family.label h),
    let o := registered z axis
    let T := center R.family.S p tiled 0
    let H := projected R b d x s o
    let A := adjusted R V P b d x s o
    let counter := R.family.O N p c 0
    Interior (T.chamber 0) (A-counter) ∧ T.rootTest (R.family.beta N p) (A-counter) =
      T.rootTest (R.family.beta N p) (H-counter) := by
  obtain ⟨rad,step⟩ := WilsonCapturedPrimaryWardFile.original R V W P b portfolio issued
  have cases := eventually_all.mpr (fun s : Finset (Fin n) => step s (fun i=>d i.val))
  have rooms := eventually_all.mpr (fun i : Fin n => WilsonCapturedPrimaryWardRoom.original R.family J
    (rad (d i)) (d i) (V (d i)))
  have raw := eventually_all.mpr (fun i : Fin n => near_center R.family J (d i) R.makes)
  obtain ⟨N₀,native⟩ := eventually_atTop.mp (cases.and (rooms.and (raw.and (near_center R.family J h R.makes))))
  have go := WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple v (by omega)
  filter_upwards [go.eventually_ge_atTop N₀, WilsonCapturedPrimaryWardTiling.clearance R simple slow v wide φ V rad d,
    WilsonCapturedPrimaryPhysicalChamber.original R J φ,
    WilsonCapturedPrimaryPhysicalArray.original R simple slow J v wide φ] with r late clear chamber array
  dsimp only
  intro N p live tiled z nz axis s x c
  obtain ⟨entry,room,source,scalar⟩ := native N (late.trans live)
  let o := registered z axis
  let T := center R.family.S p tiled 0
  have near := chamber N p (array.2.1.le.trans live) z nz axis
  have blank : 8*‖R.family.S.place (0:Site (R.family.side N p))‖ ≤ R.family.S.a J := by
    rw [latzero R.family]; simp [(R.family.S.a_pos J).le]
  have bill := scalar tiled p 0 blank c
  have sep := clear N p live z nz axis
  constructor
  · apply inside_sub _ bill
    apply Interior.combines _ s
    intro i _
    let y := x i-b.step (d i) (N,p) (x i)
    have h := incoming_continuous (V (d i)) N p (P (d i) (N,p)) y (o i)
    have extra : Interior (T.chamber 0) (incoming R.family (V (d i)) N p (P (d i) (N,p)) y (o i)) := by
      refine ⟨?_,h.measurable,?_,(Mark.cont_envelope h).cost⟩
      · intro k U
        simp only [incoming,Source.initial,Pi.smul_apply]
        rw [(V (d i)).placed_invariant (portfolio (d i)).valid _ _ k U]
      · exact fun U Z agreed => incoming_local _ _ _ _ _ _ U Z
          (agrees_mono agreed (room i tiled p _ (near i)).2)
    exact inside_sub (source i tiled p _ (near i) _) (inside_sub (source i tiled p _ (near i) y) extra)
  · have ward := entry s p T (fun i=>x i.val) (fun i=>o i.val) (R.family.O N p c 0)
        (fun i j ne=>sep i.val j.val (fun h=>ne (Subtype.ext h)))
        (fun i=>(room i.val tiled p _ (near i.val)).1)
        (fun i=>source i.val tiled p _ (near i.val)) (fun i=>(room i.val tiled p _ (near i.val)).2) bill
    have left : (fun U => ∏ i : s, R.family.O N p (b.step (d i.val) (N,p) (x i.val)) (o i.val) U) =
        projected R b d x s o := funext (fun U=>s.prod_attach
          (fun i : Fin n => R.family.O N p (b.step (d i) (N,p) (x i)) (o i) U))
    have right : (fun U => ∏ i : s, (R.family.O N p (x i.val) (o i.val) U -
        residual R.family (V (d i.val)) N p (P (d i.val) (N,p))
          (x i.val-b.step (d i.val) (N,p) (x i.val)) (o i.val) U)) =
        adjusted R V P b d x s o := funext (fun U=>s.prod_attach (fun i : Fin n =>
          R.family.O N p (x i) (o i) U - residual R.family (V (d i)) N p (P (d i) (N,p))
            (x i-b.step (d i) (N,p) (x i)) (o i) U))
    rw [left,right] at ward
    exact ward.symm

end YM.Integration.WilsonCapturedPrimaryWardFaces
