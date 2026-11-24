import YM.Integration.WilsonThermometerIntrinsicRoster
import YM.Integration.WilsonThermometerMarchFaces
import YM.Integration.WilsonPositionThermometerGradedSource

/-! The native offset circuit and its intervening radii on the complete
graded thermometer. The reporting date and tariff precede all cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchRoster
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open scoped Classical Topology
set_option quotPrecheck false
open WilsonPositionThermometerGradedSource
variable {G : Gauge} (R : Run G)
local notation "d" => (fun i : Fin 3 => (grade i).val)
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "names" => Stock.census (Fin 3)

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b) :
    ∃ t ≥ 9, ∀ᶠ m : ℕ in atTop, ∀ p N (hm : m ≤ N) (z : Fin 3 → Site (R.family.side N p)),
      (∀ i i' : Fin 3, i ≠ i' → (R.family.path.levels.budget m).B^2 <
        separation (WilsonThermometerOwnOffsetJoint.origins R z m i)
          (WilsonThermometerOwnOffsetJoint.origins R z m i')) →
      ∃ (V : (i : Fin 3) → Sight R.family (d i) p) (r : (i : Fin 3) → Emblems R.family (d i)),
        (∀ i, Enrolled R.makes R.doors B m N p (d i) (digits R N p (z i)) (V i) (r i)) ∧
        (∀ y : (i : Fin 3) → Palette R.family (d i), (∀ i, size (y i) ≤ 1) →
          WilsonThermometerIntrinsicRoster.filed R d z y V r names hm t) ∧
        ∀ j ≥ m, ∀ s : (Stock.census (Fin 3)).Mode, WilsonThermometerMarchFaces.inverse R t m j s ≤
          β j ^ (3*(t+1)*(j-m+1)) := by
  obtain ⟨t, ht, ready⟩ := WilsonThermometerIntrinsicRoster.original R simple shop 6
  refine ⟨t, ht, ?_⟩
  filter_upwards [ready] with m issued
  intro p N hm z sep
  obtain ⟨V,r,hV,hy⟩ := issued p N hm (Fin 3) d (fun i => Nat.lt_succ_iff.mp (grade i).isLt) z sep
  exact ⟨V,r,hV,hy names,fun j hj s => WilsonThermometerMarchFaces.face R simple t m j hj s⟩

end YM.Integration.WilsonThermometerMarchRoster
