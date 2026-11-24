import YM.Integration.WilsonPhysicalHistoryFieldBank
import YM.Integration.FVA1Physical.Wilson.IteratedBankGate

/-! Apply the original iterated angular-bank receipt to the independent
finite-period field of the same run, including all vanishing higher ranks. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryFieldEnrollment
open Filter Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep RG16.Literal RG16.Guarding
open MSbar MSbar.Whisk Push.Uniform
open scoped Classical Topology
variable {G : Gauge} {d D : ℕ}

theorem on_run (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
    (a : hue G) (depth : d<D) (simple : G.Simple) {u : ℕ→ℕ}
    (grant : WilsonWindowFormalPurchase.Canonical u R.kit)
    (o : Loc G 1) (s p : ℕ) {δ : ℝ} (δ0 : 0<δ) :
    ∀ᶠ i : ℕ in atTop, ∀ (w : Letter (R.family.labels.level d)) (N : ℕ), i≤N →
      ∀ (f : Studio D), ‖Annex.compress D f‖≤1 → ∀ n : Side,
      let β := R.family.path.levels.clock.hatBeta i
      let z := (Lotus.drip n (0,o)).1
      let Q := WilsonPhysicalHistoryFieldBank.primary n (Kemp.banner d (graph R L a depth N i w f) n)
      FVA1Physical.Wilson.BankPaid z β s p (d+p) δ Q ∧
      ∀ e ≤ p, ∀ h : ℕ, Whisk.Vault (Measuring.chart n G) {z} (Mosaic.αm β)
        s h 0 (PowerSeries.coeff e Q) (β^δ) := by
  filter_upwards [WilsonPhysicalHistoryFieldBank.same_run R L a depth simple grant o s p δ0] with i bank
  intro w N live f unit n
  let β := R.family.path.levels.clock.hatBeta i
  let Q := WilsonPhysicalHistoryFieldBank.primary n (Kemp.banner d (graph R L a depth N i w f) n)
  have paid : FVA1Physical.Wilson.BankPaid (Lotus.drip n (0,o)).1 β s p (d+p) δ Q :=
    bank w N live f unit n
  exact ⟨paid,fun _ he h => paid.through h he⟩

end YM.Integration.WilsonPhysicalHistoryFieldEnrollment

