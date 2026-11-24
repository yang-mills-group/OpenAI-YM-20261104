import YM.Integration.WilsonCapturedPrimaryWardRoom

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardTiling
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction Extra.Histories PhysicalNext.Repeat.Legato
open RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat Legato Bandage
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells
open XSpace XSpace.Rose Push.GridApprox OPE OPE.Orbits
open WilsonPositionThermometerCapStation WilsonOffsetReportingProducts WilsonOffsetEquationLaw
open WilsonAddressedEquationShelf WilsonCapturedPrimaryPhysicalArray
open private supported from YM.Integration.WilsonCapturedPrimaryPhysicalArray
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {n : ℕ}
local notation "B" j:max => (((R.family).path.levels.budget j).B)

private theorem protects (V : ∀ d, SectionData ((R.family).labels.level d))
    (rad : ℕ → ℕ) (d : Fin n → ℕ) : ∃ H : ℕ, ∀ᶠ N : ℕ in atTop,
    ∀ p (o : Fin n → Site ((R.family).side N p)), (∀ i j, i ≠ j → H < separation (o i) (o j)) →
      Avoids (C:=R.family) V rad d o := by
  choose v fv using fun i : Fin n => WilsonSeparatedOffsetSites.footprint (C:=R.family) (V (d i))
  choose a fa using fun i : Fin n => WilsonSeparatedOffsetSites.footprint (C:=R.family) ((R.family).localSection (d i))
  let H := univ.sup (fun i=>rad (d i)) + max (univ.sup v) (univ.sup a)
  refine ⟨H,?_⟩
  filter_upwards [eventually_all.mpr fv,eventually_all.mpr fa] with N vs ys
  intro p o gaps i j ne
  have rh : rad (d i) ≤ univ.sup (fun i=>rad (d i)) := Finset.le_sup (f:=fun i=>rad (d i)) (mem_univ i)
  have av := Finset.le_sup (f:=v) (mem_univ j)
  have ay := Finset.le_sup (f:=a) (mem_univ j)
  have cut := gaps j i ne.symm
  dsimp only [H] at cut
  constructor
  · intro z hz
    have near := ys j p (o j) z hz
    have tri := separation_triangle (o j) z (o i)
    rw [separation_comm (o j) z] at tri
    change rad (d i) < separation z (o i)
    omega
  · intro z hz
    have near := vs j p (o j) z hz
    have tri := separation_triangle (o j) z (o i)
    rw [separation_comm (o j) z] at tri
    change rad (d i) < separation z (o i)
    omega

/-- The actual supported microscopic tuple clears each alternate Ward stencil at every period. -/
theorem clearance (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v : ℕ) (wide : 4 < v) (φ : Test n) (V : ∀ d, SectionData ((R.family).labels.level d))
    (rad : ℕ → ℕ) (d : Fin n → ℕ) :
    ∀ᶠ r : ℝ in 𝓝[>]0, let k := WilsonMeasuredWindow.stop (R.family).path.levels simple v r
    ∀ N p, k ≤ N → ∀ z : Fin n → Site ((R.family).side N p), WilsonCenteredCompactBooking.mass R φ r (N,p) z ≠ 0 →
    ∀ a : Option (Fin n), Avoids (C:=R.family) V rad d (registered z a) := by
  obtain ⟨H,tail⟩ := protects R V rad d
  obtain ⟨s,paid⟩ := eventually_atTop.mp tail
  have go := WilsonMeasuredWindow.stop_tendsto (R.family).path.levels simple v (by omega)
  have grow := (Multi.Wage.ranges simple (R.family).path.levels).comp go
  filter_upwards [go.eventually_ge_atTop s,grow.eventually_ge_atTop (H+2),
    WilsonCapturedPrimarySeparatedStop.translated R simple slow v wide φ] with r late ample apart
  let k := WilsonMeasuredWindow.stop (R.family).path.levels simple v r
  dsimp only
  intro N p live z nz axis
  apply paid N (late.trans live) p
  intro i j ne
  obtain ⟨x,hx,site_eq⟩ := supported R φ r z nz
  have pos (u : Fin n) : wrap ((R.family).side N p) (address ((R.family).S.a N) (r • x) u) = z u :=
    congrFun site_eq u
  have low := apart N p live x hx (axis.elim 0 z) i j ne
  rw [pos i,pos j] at low
  change (B k)^2 < separation (((R.family).S.toDepth live p).parent (registered z axis i))
    (((R.family).S.toDepth live p).parent (registered z axis j)) at low
  have up := Work.E04.parent_separation ((R.family).S.toDepth live p) (registered z axis i) (registered z axis j)
  change H+2 ≤ B k at ample
  have enough : B k ≤ (B k)^2 := by nlinarith only [ample]
  omega

variable (V : ∀ d, SectionData ((R.family).labels.level d)) (W : Mark.Weave G)
  (P : ∀ d, (ℕ×ℕ) → ((R.family).label d ≃ₗ[ℂ] (R.family).label d)) (b : Presentation (R.family))
  (portfolio : ∀ d, Mark.Portfolio (R.family).params (V d) (W d))
  (issued : Hearthside (R.family) V W P b (Bandage.fly R.alloy.B.a))
include W portfolio issued in
/-- All the geometric premises of the reflected Ward comparison on original microscopic cells.
    The one filed output may depend on the tuple and the cutoff. -/
theorem original (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v J h : ℕ) (wide : 4 < v) (d : Fin n → ℕ) (φ : Test n) :
    ∀ᶠ r : ℝ in 𝓝[>]0, let k := WilsonMeasuredWindow.stop (R.family).path.levels simple v r
    ∀ N p (_live : k ≤ N) (tiling : J ≤ N) (z : Fin n → Site ((R.family).side N p)),
    WilsonCenteredCompactBooking.mass R φ r (N,p) z ≠ 0 →
    ∀ (a : Option (Fin n)) (x : (i : Fin n) → (R.family).label (d i)) (c : (R.family).label h),
    let o := registered z a
    let T := center (R.family).S p tiling 0
    T.rootTest ((R.family).beta N p) ((fun U => ∏ i, (R.family).O N p (b.step (d i) (N,p) (x i)) (o i) U) - (R.family).O N p c 0) =
    T.rootTest ((R.family).beta N p) ((fun U => ∏ i, ((R.family).O N p (x i) (o i) U -
      residual (R.family) (V (d i)) N p (P (d i) (N,p)) (x i - b.step (d i) (N,p) (x i)) (o i) U)) - (R.family).O N p c 0) := by
  obtain ⟨rad,ward⟩ := WilsonCapturedPrimaryWardFile.original R V W P b portfolio issued
  have stocks := eventually_all.mpr (fun i : Fin n =>
    WilsonCapturedPrimaryWardRoom.original (R.family) J (rad (d i)) (d i) (V (d i)))
  have originals := eventually_all.mpr (fun i : Fin n => near_center (R.family) J (d i) R.makes)
  obtain ⟨N₀,ready⟩ := eventually_atTop.mp ((ward (Fin n) d).and (stocks.and (originals.and (near_center (R.family) J h R.makes))))
  have go := WilsonMeasuredWindow.stop_tendsto (R.family).path.levels simple v (by omega)
  filter_upwards [go.eventually_ge_atTop N₀, clearance R simple slow v wide φ V rad d,
    WilsonCapturedPrimaryPhysicalChamber.original R J φ,
    WilsonCapturedPrimaryPhysicalArray.original R simple slow J v wide φ] with r late apart chamber array
  dsimp only
  intro N p live tiled z nz a x c
  obtain ⟨file,room,orig,counter⟩ := ready N (late.trans live)
  have located := chamber N p (array.2.1.le.trans live) z nz a
  have blank : 8*‖(R.family).S.place (0:Site ((R.family).side N p))‖ ≤ (R.family).S.a J := by
    rw [latzero (R.family)]; simp [(R.family).S.a_pos J |>.le]
  exact file p (center (R.family).S p tiled 0) x (registered z a) ((R.family).O N p c 0)
    (apart N p live z nz a) (fun i=>(room i tiled p _ (located i)).1)
    (fun i=>orig i tiled p _ (located i)) (fun i=>(room i tiled p _ (located i)).2)
    (counter tiled p 0 blank c)

end YM.Integration.WilsonCapturedPrimaryWardTiling
