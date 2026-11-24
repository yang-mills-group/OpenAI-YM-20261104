import YM.Integration.ActualIndependentTests
import YM.RemainderComparison.Placement.Input

/-!
Realize the marked input on an already specified representation. The supplied
registration and zero-activity receipts refer to that exact `R`; no new
representation is substituted on the strength of equal evaluated densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson RG RemainderComparison RemainderComparison.Typeface
open RemainderComparison.Placement
open PhysicalNext.Repeat
open Push.AbsoluteSums.Animals

variable {G : Gauge} {f : Side} {α : Type*} {q e : ℕ} {A : ℝ}

/-- The original stencil, mask, root and computed weight, on the same `R`. -/
theorem registered_stencil_portrait (R : Rep G f)
    (D : Tile G α q e A) (base : α) (x : Site f) (j : ℕ)
    (hβ : 0 < R.beta)
    (hreg : R.activities.reg j = Tile.aperture x e)
    (hzero : R.activities.E j = 0) :
    ∃ M : Portrait R α,
      M.wing = Lotus.Wing.logKey j ∧
      M.weight = Tile.peso G q e A R.p ∧
      ∀ t, (M.angle t).ingredient =
        masked R.p.threshold (neighbors e x) (Tile.read D x t) := by
  obtain ⟨M, hwing, hweight, hread⟩ :=
    Sagas.Packet.ready (R := R) (Tile.script D x base) hβ hreg hzero
  refine ⟨M, hwing, hweight.trans (Tile.enumerates D x base R.p R.beta hβ), ?_⟩
  intro t
  rw [hread, Tile.delivers (hb := hβ)]
  rfl

variable {ι : Type} {αs : ι → Type*} {qs es : ι → ℕ} {As : ι → ℝ}

/-- Independent slot choices retain the literal stencil identities and common
computed prices, including when the test spaces differ between slots. -/
theorem registered_independent_portraits (R : Rep G f)
    (D : ∀ i, Tile G (αs i) (qs i) (es i) (As i))
    (base : ∀ i, αs i) (x : ι → Site f) (j : ι → ℕ)
    (hβ : 0 < R.beta)
    (hreg : ∀ i, R.activities.reg (j i) = Tile.aperture (x i) (es i))
    (hzero : ∀ i, R.activities.E (j i) = 0) :
    ∃ M : ∀ i, Portrait R (αs i),
      (∀ i, (M i).wing = Lotus.Wing.logKey (j i)) ∧
      (∀ i, (M i).weight = Tile.peso G (qs i) (es i) (As i) R.p) ∧
      ∀ tests i, ((independentPortraits M i).angle tests).ingredient =
        masked R.p.threshold (neighbors (es i) (x i))
          (Tile.read (D i) (x i) (tests i)) := by
  choose M hwing hweight hread using fun i =>
    registered_stencil_portrait R (D i) (base i) (x i) (j i) hβ (hreg i) (hzero i)
  exact ⟨M, hwing, hweight, fun tests i => hread i (tests i)⟩

end YM.Integration
