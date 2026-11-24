import YM.Integration.WilsonNeutralOffsetCutoff
import YM.Integration.WilsonReflectedPhysicalFiling
import YM.Integration.WilsonThermometerCourseIntake

/-! The true factory label at every reflected child, with its own
microscopic position and the engineering factor from the actual arm. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryFiledArms
open Filter Lattice Wilson RG Source PhysicalNext.Repeat.Legato RG16 RG16.Literal
open RG05Readout Native Address Many Records Harvest Copper
open WilsonThermometerOwnOffsetField
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {D N p k : ℕ} (d : I → ℕ) (sites : I → Site (R.family.side N p))
local notation "P" => R.family

def entered (V : (i : I) → Sight P (d i) p) (r : (i : I) → Emblems P (d i)) : Prop :=
  ∀ i, WilsonThermometerOffsetTrajectory.Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R)
    k N p (d i) (WilsonThermometerOffsetResidue.digits R N p (sites i)) (V i) (r i)

omit [DecidableEq I] [Nonempty I] in
theorem election (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b) :
    ∀ᶠ j : ℕ in atTop, ∀ N p (_ : j ≤ N) (sites : I → Site ((P).side N p)),
    ∃ V r, entered R d sites (k:=j) V r := by
  have all := Filter.eventually_all.mpr fun i : I =>
    (WilsonThermometerOffsetLedger.original R simple shop (d i)).mono (fun _ h => h.1)
  filter_upwards [all] with j awake N p live sites
  choose V r billed using fun i => WilsonThermometerOffsetTrajectory.enroll R.makes
    (awake i) live (WilsonThermometerOffsetResidue.digits R N p (sites i))
  exact ⟨V,r,billed⟩

variable (cap : ∀ i, d i ≤ D) (V : (i : I) → Sight P (d i) p)
variable (r : (i : I) → Emblems P (d i)) (entry : entered R d sites (k:=k) V r)

def arm (cap : ∀ i, d i ≤ D) (V : (i : I) → Sight P (d i) p)
    (r : (i : I) → Emblems P (d i)) (entry : entered R d sites (k:=k) V r) (y : (i : I) → Palette P (d i)) : WilsonReflectedPhysicalFiling.Arms R I D N p k where
  sites := sites
  grade := d
  limited := cap
  viewer := V
  sections := r
  enrolled := entry
  vector := fun i => (WilsonNeutralOffsetCutoff.weight R (y i) : ℂ) • y i
  bounded := fun i => (WilsonNeutralOffsetCutoff.unit_budget R (y i)).2

def rent (y : (i : I) → Palette P (d i)) : ℝ := ∏ i, (1 + size (y i))

omit [DecidableEq I] [Nonempty I] in
theorem positive (y : (i : I) → Palette P (d i)) : 0 < rent R d y :=
  Finset.prod_pos fun i _ => by linarith [size_ge (y i)]

omit [DecidableEq I] [Nonempty I] in
theorem read (cap : ∀ i, d i ≤ D) (V : (i : I) → Sight P (d i) p)
    (r : (i : I) → Emblems P (d i)) (entry : entered R d sites (k:=k) V r) (live : k ≤ N) (x : (i : I) → (P).label (d i)) (y : (i : I) → Palette P (d i))
    (hit : ∀ i, ((P).factory (d i) N p).terminal (finer (r i) live (y i) (primaryLetter (d i))) =
       (((P).S.a k : ℂ)^(d i))⁻¹ • x i) :
    WilsonReflectedPhysicalFiling.reading (I:=I) R (arm R d sites cap V r entry y) live =
       ((rent R d y : ℂ)⁻¹ • fun U => ∏ i, (P).O N p (x i) (sites i) U) := by
  funext U
  change (∏ i, WilsonThermometerIntrinsicRoster.source R d sites (fun j => (WilsonNeutralOffsetCutoff.weight R (y j):ℂ) • y j) r live i U) = _
  have leg (i : I) := congrFun (WilsonNeutralOffsetCutoff.source_of_primary R (r i) live
    (x i) (sites i) (WilsonNeutralOffsetCutoff.weight R (y i) : ℂ) (y i) (hit i)) U
  calc
    _ = ∏ i, ((WilsonNeutralOffsetCutoff.weight R (y i) : ℂ) * (P).O N p (x i) (sites i) U) :=
      Finset.prod_congr rfl fun i _ => leg i
    _ = _ := by simp [Finset.prod_mul_distrib, WilsonNeutralOffsetCutoff.weight, rent,
        Finset.prod_inv_distrib]

omit [DecidableEq I] [Nonempty I] in
theorem original (cap : ∀ i, d i ≤ D) (V : (i : I) → Sight P (d i) p)
    (r : (i : I) → Emblems P (d i)) (entry : entered R d sites (k:=k) V r) (live : k ≤ N) (x : (i : I) → (P).label (d i)) :
    let y := fun i => WilsonNeutralOffsetCutoff.input R (p:=p) (r i) live (x i)
    WilsonReflectedPhysicalFiling.reading (I:=I) R (arm R d sites cap V r entry y) live =
      ((rent R d y : ℂ)⁻¹ • fun U => ∏ i, (P).O N p (x i) (sites i) U) :=
  by intro y; exact read R d sites cap V r entry live x y (fun i => WilsonNeutralOffsetCutoff.launched R (r i) live (x i))

end YM.Integration.WilsonCapturedPrimaryFiledArms
