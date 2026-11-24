import YM.Integration.WilsonPhysicalHistoryFormalMatrices
import YM.FormalBulk08.Trellis.Ferment

/-! Identify the dated reclosed inverse with the manuscript's actual
Trellis inverse return in the coupling coordinates of its reporting stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryFormalReturn

open Filter Real Function Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis
open Planned.PrimaryIntegral295 Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep WilsonPhysicalHistoryFormalMatrices
open scoped Classical BigOperators Matrix

variable {G : Gauge} (R : Run G) {d D : ℕ}
variable (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch)) (a : hue G) (depth : d<D)

/-- The genuine nonlinear step determined by the original evolving vacuum. -/
def day (N i : ℕ) : Pence :=
  Roof.epoch a (destination R.family.path.levels N i) (L i) R.family.path.levels.clock.kernel
    (Dove.model (K:=R.family.path.levels.clock.kernel) R.family.path.levels L
      (fun b=>(R.family.path.levels.blocks b 0).branches) R.metals.O a N (i+1))
    R.metals.O (R.family.path.levels.blocks i 0).branches

private theorem shift (N i k : ℕ) (q : Pence) :
    flow (day R L a N) k i (reset R L a N i q) = flow (day R L a N) k (i+1) q := by
  rw [Trellis.next_level]
  apply congrArg
  unfold WilsonPhysicalHistoryFormalMatrices.reset
  rw [Roof.rele,mul_comm,forward_green]
  rfl

/-- The original inverse product, in the coordinates of *any* reporting
    stage k. In particular the chronological inverse at its first stage is
    exactly the original stored return, not a separately stipulated one. -/
theorem ambient (N k i n : ℕ) :
    let K := day R L a N
    let B := matrix R L a depth N
    Trellis.ropes K B k i n = (flow K k i).mapMatrix (strings R L a depth N n i).2 := by
  induction n generalizing i with
  | zero =>
    change (1 : Tilework (R.family.labels.level d)) = (flow _ _ _).mapMatrix 1
    rw [map_one]
  | succ n ih =>
    let K := day R L a N
    let B := matrix R L a depth N
    let F (j : ℕ) : Tilework (R.family.labels.level d) →+* Tilework (R.family.labels.level d) :=
      (flow K k j).mapMatrix
    let S : Tilework (R.family.labels.level d) →+* Tilework (R.family.labels.level d) := (reset R L a N i).mapMatrix
    let Q := (strings R L a depth N n (i+1)).2
    have commute : F i (S Q) = F (i+1) Q := by
      ext1 x y
      exact shift R L a N i k (Q x y)
    have head : Trellis.ropes K B k i 1 = F i (B i)⁻¹ := by
      change Trellis.ropes K B k i (0+1) = F i (B i)⁻¹
      rw [ropes_grow]
      change F i (B i)⁻¹*1 = F i (B i)⁻¹
      rw [mul_one]
    have tail : Trellis.ropes K B k (i+1) n = F (i+1) Q := ih (i+1)
    change Trellis.ropes K B k i (n+1) = F i (S Q*(B i)⁻¹)
    rw [show n+1=1+n by omega,ropes_split,head,tail,map_mul,commute]

/-- The displayed dimensionless inverse matrix in the original formal
    source, with the correct reporting subtraction coordinate. -/
theorem original (N i n : ℕ) :
    Trellis.ropes (day R L a N) (matrix R L a depth N) i i n = (strings R L a depth N n i).2 := by
  rw [ambient R L a depth N i i n]
  ext1 x y
  exact from_self _ _ _

theorem returned (simple : G.Simple) (o : Loc G 1) :
    ∀ᶠ k : ℕ in atTop, ∀ (N i n : ℕ), k ≤ i → i+n ≤ N →
      let F := R.family.labels.level d
      let V := (strings R L a depth N n i).1
      let U := Trellis.ropes (day R L a N) (matrix R L a depth N) i i n
      V*U=1 ∧ U*V=1 ∧ ∀ x y e, slots F y+e < slots F x → coeff e (U x y)=0 := by
  filter_upwards [reclosed R L a depth simple o] with k ready
  intro N i n ki cap F V U
  obtain ⟨forward,backward,powers,_⟩ := ready N n i ki cap
  have eqn : U=(strings R L a depth N n i).2 := original R L a depth N i n
  rw [eqn]
  exact ⟨forward,backward,fun x y e high=>(powers x y e high).2⟩

end YM.Integration.WilsonPhysicalHistoryFormalReturn

