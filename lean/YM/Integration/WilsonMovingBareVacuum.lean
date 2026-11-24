import YM.Integration.WilsonMovingTaylorConvention
import YM.Integration.WilsonRunFormalMarkedStep

/-! The formal UV vacuum and the Wilson moving chart have the same complete
Taylor tensor. The full Gaussian quadratic is retained until it is removed
from the positive coupling part of the microscopic interaction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingBareVacuum
open Function PowerSeries Lattice Exterior Wilson Precision Tree Stationary Push.Uniform Bloch
open RG PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent Next.Free
open FormalBulk08 Jets Flat Reef Mesa Dove Lotus Shore Gorge City Cork Rift Lava Kemp Pose Glide
open Bank Dawn Wine Rial Roof Planned.PrimaryIntegral295
open scoped Classical BigOperators ContDiff

def energy (G : Gauge) (n : Side) (v : Jets.Rays (Primary n G)) :=
  Wilson.energy (represent (tint G (Body 1 n) v))

def seed (G : Gauge) (n : Side) :=
  PowerSeries.map (MvPolynomial.rename (WilsonMovingGaussianCoordinates.link G n).symm).toRingHom
    (Mesa.stone (Mesa.Enter G) n)

theorem positions (G : Gauge) (n : Side) :
    seed G n = -afterX (paste (energy G n)) 2 := by
  let s := (WilsonMovingGaussianCoordinates.link G n).symm
  have fields : energy G n = fun x : Jets.Rays (Primary n G) => Reef.fundamental G n (x ∘ s) := rfl
  have mapped := WilsonMovingTaylorConvention.placed s (Reef.fundamental G n)
    ((Reef.front (G:=G) (n:=n)).of_le le_top)
  apply PowerSeries.ext
  intro i
  rw [seed, ← Mesa.top_word, Reef.seed, PowerSeries.coeff_map, map_neg, map_neg,
    map_neg, after_one, after_one, fields, ← mapped, PowerSeries.coeff_map]

def released (G : Gauge) (n : Side) :=
  seed G n - PowerSeries.C (coeff 0 (seed G n))

theorem quadratic (G : Gauge) (n : Side) :
    coeff 0 (released G n) = 0 ∧
      coeff 0 (seed G n) = -WilsonMovingTaylorConvention.tensor (energy G n) 2 := by
  constructor
  · simp [released]
  · rw [positions, map_neg, after_one, Nat.add_zero, WilsonMovingTaylorConvention.coefficient]

theorem positive (G : Gauge) (n : Side) (i : ℕ) :
    coeff (i+1) (released G n) = -WilsonMovingTaylorConvention.tensor (energy G n) (2+(i+1)) := by
  have zero : coeff (i+1) (PowerSeries.C (coeff 0 (seed G n))) = 0 := by simp
  rw [released, map_sub, zero, sub_zero, positions, map_neg, after_one,
    WilsonMovingTaylorConvention.coefficient]

/-- The independent vacuum on the very same physical upper date and period,
with the original schedule and chart. -/
theorem onRun {G : Gauge} (R : Run G)
    (L : ∀ i, Lodge ((R.alloy.B.a.clock.op i 0).patch)) (a : hue G) (N per : ℕ) :
    let M := Dove.model (K:=R.alloy.B.a.clock.kernel) R.alloy.B.a L
      (fun i => (R.family.path.levels.blocks i 0).branches) R.metals.O a N N
    let n := R.family.side N per
    PowerSeries.map (MvPolynomial.rename (WilsonMovingGaussianCoordinates.link G n).symm).toRingHom
      (Mesa.stone M n) = -afterX (paste (energy G n)) 2 := by
  dsimp only
  rw [Dove.leaves]
  exact positions ..

end YM.Integration.WilsonMovingBareVacuum
end
