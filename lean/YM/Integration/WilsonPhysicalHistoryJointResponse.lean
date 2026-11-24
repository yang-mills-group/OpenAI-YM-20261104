import YM.Integration.WilsonPhysicalHistoryJointInputs
import YM.Integration.WilsonMovingRunWickCoordinates

/-! The whole funded input belongs to one old-vacuum normalized block, in
both the prescribed finite formal presentation and its original physical coordinates. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryJointResponse
open Filter Function Finset Lattice Exterior Wilson RG Precision Tree Matrix Bloch Push.Uniform
open Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open FormalBulk08 Flat Reef Orb Next.Free Jets MSbar.Rolling MSbar.Cacao PowerSeries
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Place Film Carrier WilsonRunFormalMarkedStep
open Source Source.Drops Labels RG16.Literal RG16.Guarding
open WilsonMovingPolynomialPull WilsonConditionalTaylorWick WilsonPhysicalHistoryBlockInputs
open scoped Classical Topology Matrix BigOperators
variable {G : Gauge} {d D q : ℕ}
variable (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
variable (a : hue G) (depth : d<D)

/-- The prescribed preimage-wise product, before any conditional is taken. -/
def joint (N i : ℕ) (n : Side) (w : Fin q → Letter (R.family.labels.level d))
    (x : Fin q → Site (R.family.S.block i)) (f : Fin q → Studio D) (mask : Finset (Fin q)) :
    Pap (wire G n) :=
  ∏ j∈mask, Kemp.resite (wrap n (lift (x j)))
    (Kemp.banner d (graph R L a depth N (i+1) (w j) (Dawn.throughW (x j) D (block R i) (f j))) n)

/-- The signed normalized receiver consumes exactly the product whose physical
angular seminorm was paid; no change of incoming polynomial is involved. -/
theorem placed (N i : ℕ) (n : Side) (w : Fin q → Letter (R.family.labels.level d))
    (x : Fin q → Site (R.family.S.block i)) (f : Fin q → Studio D) (mask : Finset (Fin q)) :
    WilsonMovingPolynomialPull.place (WilsonMovingGaussianCoordinates.link G n).symm
      (joint R L a depth N i n w x f mask) =
      ∏ j∈mask, incoming R L a depth N i n (x j) (w j) (f j) := by
  classical
  unfold WilsonMovingPolynomialPull.place joint
  rw [map_prod]
  rfl

/-- Exactly the filed old interaction of the same trajectory, at the incoming stage. -/
def prior (N i per : ℕ) : Pap (wire G (R.family.S.side (i+1) per)) :=
  let V := R.family.path.levels
  Mesa.stone (Dove.model V L (fun k=>(V.blocks k 0).branches) R.metals.O a N (i+1))
    (R.family.S.side (i+1) per)

theorem on_run (simple : G.Simple) {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit)
    (pace : WilsonWindowReportingPace.Slow R.kit) (o : Loc G 1) (s p q : ℕ) {δ : ℝ} (δ0 : 0<δ) :
    ∀ᶠ i : ℕ in atTop, ∀ (N per : ℕ) (hi : i<N) (base : Site (R.family.S.block i))
      (w : Fin q → Letter (R.family.labels.level d)) (x : Fin q → Site (R.family.S.block i))
      (f : Fin q → Studio D), (∀ j, ‖f j‖≤1) → ∀ mask : Finset (Fin q),
      let fine := R.family.S.side (i+1) per
      let B := joint R L a depth N i fine w x f mask
      let X := prior R L a N i per
      let B' := WilsonMovingPolynomialPull.place (WilsonMovingGaussianCoordinates.link G fine).symm B
      let S := R.family.path.levels.clock.op i per
      let K := (RunFormalChain.fromRun R).step N i per hi
      let P := destination R.family.path.levels N i
      let A := Bloch.installed S.ratio (P.duo R.family.path.levels.clock.kernel.penalty).A0
      FVA1Physical.Wilson.BankPaid (wrap fine (lift base)) (R.family.path.levels.clock.hatBeta (i+1))
        s p (q*(d+p)) δ B' ∧
      ∀ (F : Forest S.ratio) (tag : S.Choices) (t : Positions (Primary (R.family.S.side i per) G)),
        let y := FreeResolvent.flatten (tint G (Body 1 (R.family.S.side i per)) t)
        WilsonConditionalTaylorWick.quotient (WilsonMovingFiniteConditional.lift (wire G (R.family.S.side i per)) _)
          (Sum.elim (Flat.rawMean G S F A *ᵥ y) y) (Flat.testPrecision G S F P.wing)⁻¹
          (WilsonMovingFiniteConditional.interaction (Reef.flush F tag R.metals.O X)) (Reef.seat F B) =
        WilsonConditionalTaylorWick.quotient (straight F G) (poring F (K.b F) *ᵥ t) (K.covariance F tag)
          (barbed F tag R.metals.O (splitV (WilsonMovingPolynomialPull.place
            (WilsonMovingGaussianCoordinates.link G fine).symm X)))
          (PowerSeries.map (rail (taps F G)).toRingHom B') := by
  filter_upwards [WilsonPhysicalHistoryJointInputs.on_run R L a depth simple grant pace o s p q δ0] with i ticket
  intro N per hi base w x f unit mask
  dsimp only
  constructor
  · rw [placed]
    exact (ticket N hi (R.family.S.side (i+1) per) base w x f unit mask).1
  · intro F tag t
    exact WilsonMovingRunWickCoordinates.source R N i per hi F tag t (prior R L a N i per)
      (joint R L a depth N i (R.family.S.side (i+1) per) w x f mask)

end YM.Integration.WilsonPhysicalHistoryJointResponse

