import YM.Integration.WilsonTrueProjectedPointInverse
import YM.Integration.WilsonCapturedPrimaryPointBasis

/-! The finite inverse-tuned section submitted at a reporting date.
We keep the entire upper series and the measured lower point coordinates.
Testing the genuine bare section at a child keeps its derivative letters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionReturnedAxes
open Function Finset Lattice Wilson RG Source Source.Drops Labels
open FormalBulk08 Lotus Shore Gorge Rift Lava Kemp Pose Glide Dawn Rial Reef
open PowerSeries City Mesa PhysicalNext Repeat Legato Trace.Physical
open scoped Classical BigOperators
variable {G : Gauge} {d D : ℕ}

/-- A whole returned point vector in the original zero-derivative coordinates. -/
def target (F : Frame G d) (c : F.Index → ℂ) (u : Letter F) : PowerSeries ℂ :=
  ∑ b, if u = WilsonCapturedPrimaryPointBasis.axis F b then PowerSeries.C (c b) else 0

theorem point (F : Frame G d) (c : F.Index → ℂ) (b : F.Index) :
    target F c (WilsonCapturedPrimaryPointBasis.axis F b) = PowerSeries.C (c b) := by
  simp [target,WilsonCapturedPrimaryPointBasis.axis_eq]

variable (R : Run G) (wood : Primer.Families R.family) (a : hue G) (depth : d < D)
    (digit : ∀ i, Site (R.family.S.block i))
local notation "F₀" => R.family.labels.level d

def upper (N s : ℕ) (g : ℕ → ℝ) (c : (F₀).Index → ℂ) : Letter F₀ → PowerSeries ℂ :=
  WilsonTrueProjectedPointInverse.lift R wood a depth digit N s g (target F₀ c) (N-s)

theorem returned (N s q : ℕ) (g : ℕ → ℝ) (c : (F₀).Index → ℂ)
    (simple : G.Simple) (loc : Stationary.Loc G 1) (front : d ≤ R.family.path.levels.clock.J (s+1))
    (live : s ≤ N) :
    WilsonTrueProjectedPointProgram.income R wood a depth digit N N q g
      (WilsonTrueProjectedPointInverse.take R q (upper R wood a depth digit N s g c)) s =
        WilsonTrueProjectedPointInverse.take R q (target F₀ c) := by
  simpa [upper,WilsonTrueProjectedPointInverse.lift] using
    WilsonTrueProjectedPointInverse.original R wood a depth digit N s q g (target F₀ c)
      simple loc front s le_rfl live

def test (F : Frame G d) (depth : d < D) (p : Studio D) (u : Letter F) : ℝ :=
  Dawn.notch (pet F u) ((Dawn.paper_fits (pet F u)).trans (Nat.le_trans d.le_succ depth)) p

def submit (F : Frame G d) (depth : d < D) (p : Studio D) (v : Letter F → PowerSeries ℂ)
    (b : F.Index) : PowerSeries ℂ :=
  ∑ u : Letter F, if mint F u = b then PowerSeries.C (test F depth p u : ℂ)*v u else 0

/-- Every Taylor degree of the top input, on the actual local SectionData read.
The test at this child is applied before the field coordinates are collected. -/
theorem bare (N s q : ℕ) (g : ℕ → ℝ) (c : (F₀).Index → ℂ) (p : Studio D) (read : Pot G →ₗ[ℝ] ℝ) :
    let v := upper R wood a depth digit N s g c
    ∑ b : (F₀).Index, coeff q (submit F₀ depth p v b) * (read (Rial.paperback (R.family.localSection d) b) : ℂ) =
      ∑ u : Letter F₀, coeff q (v u) * (read (Rial.sectionY (R.family.localSection d) depth u p) : ℂ) := by
  intro v
  simp only [submit,map_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_eq_single (mint F₀ u)]
  · simp [Rial.sectionY,test,coeff_C_mul]
    ring
  · intro b _ h
    simp [Ne.symm h]
  · simp

end YM.Integration.WilsonThermometerPositionReturnedAxes
end
