import YM.Integration.WilsonPhysicalHistoryTestedPairWindow
import YM.Integration.WilsonPhysicalHistoryJointResponse
import YM.Integration.WilsonRunFiniteWickCubature

/-! A recursively defined, independently prescribed mixed finite Wilson/Wick
history; a whole joint source is conditioned once at every genuine step. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryMixedChain
open Filter Function Finset Lattice Exterior Wilson RG Precision Tree Matrix Bloch Push.Uniform
open Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open FormalBulk08 Flat Reef Orb Next.Free Jets MSbar.Rolling MSbar.Cacao PowerSeries
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Place Film Carrier WilsonRunFormalMarkedStep
open Source Source.Drops Labels RG16.Literal RG16.Guarding
open WilsonMovingPolynomialPull WilsonMovingGaussianCoordinates
open scoped Classical Topology Matrix BigOperators
variable {G : Gauge}
variable (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
variable (a : hue G)

abbrev Tags (N per : ℕ) := (j:ℕ) →
  (primary (destination R.family.path.levels N j).patch R.family.path.levels.clock.kernel
    (R.family.S.side j per)).Choices

private theorem board (N per j : ℕ) :
    R.family.S.side (j+1) per = R.family.S.side j per*(destination R.family.path.levels N j).patch.L :=
  Subtype.ext (R.family.path.levels.clock.op j per).sizes

/-- Genuine independently issued whole-source transfer before evaluating
any coarse coordinates. Every factor shares the one preceding Dove vacuum. -/
def once (N per : ℕ) (tag : Tags R N per) (j : ℕ)
    (Z : Pap (wire G (R.family.S.side (j+1) per))) : Pap (wire G (R.family.S.side j per)) :=
  let V := R.family.path.levels
  let P := destination V N j
  let n := R.family.S.side j per
  let X : Pap (wire G (n*P.patch.L)) := (board R N per j) ▸ Z
  let W := Dove.model V L (fun k=>(V.blocks k 0).branches) R.metals.O a N (j+1)
  Reef.tossed P R.metals.O (V.blocks j 0).branches (L j) n (tag j) (Mesa.stone W (n*P.patch.L)) X

/-- Start with exactly one mixed terminal source. The independently prescribed
outgoing field from the previous step becomes the actual incoming polynomial
in the next formal Wick conditional. -/
def run (N per : ℕ) (tag : Tags R N per) {k t : ℕ} (kt : k ≤ t) :
    Pap (wire G (R.family.S.side t per)) → Pap (wire G (R.family.S.side k per)) :=
  Nat.leRecOn (C:=fun j => Pap (wire G (R.family.S.side j per)) → Pap (wire G (R.family.S.side k per))) kt
    (fun {j} H Z=>H (once R L a N per tag j Z)) id

@[simp] theorem at_top (N per : ℕ) (tag : Tags R N per) (k : ℕ) (Z : Pap (wire G (R.family.S.side k per))) :
    run R L a N per tag (le_refl k) Z = Z := by
  unfold run; rw [Nat.leRecOn_self]; rfl

theorem from_above (N per : ℕ) (tag : Tags R N per) {k t : ℕ} (kt : k ≤ t)
    (Z : Pap (wire G (R.family.S.side (t+1) per))) :
    run R L a N per tag (kt.trans t.le_succ) Z =
      run R L a N per tag kt (once R L a N per tag t Z) := by
  unfold run; rw [Nat.leRecOn_succ kt]

theorem rejoin (N per : ℕ) (tag : Tags R N per) {k j t : ℕ} (kj : k ≤ j) (jt : j ≤ t)
    (Z : Pap (wire G (R.family.S.side t per))) :
    run R L a N per tag kj (run R L a N per tag jt Z) = run R L a N per tag (kj.trans jt) Z := by
  induction t,jt using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
      rw [from_above R L a N per tag ht,from_above R L a N per tag (kj.trans ht)]
      exact ih _

/-- At every genuine interior stage the recorded predecessor is the single
normalized complete formal Wilson response to its own ultraviolet history.
No equality to an evolved product of singleton responses was assumed. -/
theorem adjacent (N per : ℕ) (tag : Tags R N per) {j t : ℕ} (jt : j<t)
    (Z : Pap (wire G (R.family.S.side t per))) :
    run R L a N per tag jt.le Z =
      once R L a N per tag j (run R L a N per tag jt Z) := by
  rw [← rejoin R L a N per tag j.le_succ jt Z,from_above R L a N per tag (le_refl j),at_top]

def recorded (N per : ℕ) (tag : Tags R N per) (terminal : Bool → Pap (wire G (R.family.S.side N per)))
    (j : ℕ) (part : Bool) :=
  if h : j ≤ N then
    place (link G (R.family.S.side j per)).symm (run R L a N per tag h (terminal part))
  else 0

/-- The deposited coarse polynomial is in the physical coarse primary
variables before any background chart configuration is fixed. -/
theorem current (N per : ℕ) (tag : Tags R N per) (terminal : Bool → Pap (wire G (R.family.S.side N per)))
    {j : ℕ} (live : j<N) (part : Bool) :
    recorded R L a N per tag terminal j part =
      place (link G (R.family.S.side j per)).symm (once R L a N per tag j
        (run R L a N per tag live (terminal part))) := by
  rw [recorded,dif_pos live.le,adjacent R L a N per tag live]

end YM.Integration.WilsonPhysicalHistoryMixedChain

