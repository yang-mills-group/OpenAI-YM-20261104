import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundTail
import YM.Integration.WilsonLimitConstruction.FundedWilsonSparseSupport

/-! Uniform Taylor subtraction in the original Wilson action at every
physical background. Only physical plaquettes meeting the perturbation are
charged. One original link meets six oriented plaquettes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundAction

open Function Finset Lattice Wilson RG Exterior WilsonStartup MS.Native
open FundedWilsonAtlas FundedWilsonSparseSupport
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}

def base (U : Config G n) (i : Cell n) : Quad.Group G := U ∘ edges i

def physical (U : Config G n) (B : fieldDir G n 1) (t : ℝ) :=
  Wilson.energy (increment U (t • collect G B))

def retained (d : ℕ) (U : Config G n) (B : fieldDir G n 1) (t : ℝ) :=
  ∑ i : Cell n, Work.G05.blockTaylor d
    (FundedWilsonBackgroundTail.action (Quad.mat (base U i))) (t • directions B i)

theorem plaquette (U : Config G n) (B : fieldDir G n 1) (i : Cell n) (t : ℝ) :
    FundedWilsonBackgroundTail.action (Quad.mat (base U i)) (t • directions B i) =
      G.price (faceValue (increment U (t • collect G B)) i) := by
  rw [FundedWilsonBackgroundTail.physical,←read_edges]
  rfl

/-- Inactive plaquettes cancel with their own original scalar at arbitrary
background holonomy. -/
theorem expansion (d : ℕ) (U : Config G n) (B : fieldDir G n 1) (t : ℝ) :
    physical U B t - retained d U B t = ∑ i ∈ faces B,
      FundedWilsonBackgroundTail.remainder d (Quad.mat (base U i)) (t • directions B i) := by
  simp only [physical,Wilson.energy,retained,←plaquette U B,←Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hz : directions B i = 0 := by simpa [faces] using hi
  simp [FundedWilsonBackgroundTail.remainder,hz,Work.G05.blockTaylor_zero]

theorem normalized (G : Gauge) (r : ℕ) : ∃ C > 0, ∀ (n : Side) (U : Config G n)
    (B : fieldDir G n 1), (∀ i, ‖directions B i‖ ≤ 1) → ∀ t : ℝ, t ≠ 0 → ‖t‖ ≤ 1 →
      ‖(t^2)⁻¹ * (physical U B t - retained (r+2) U B t)‖ ≤
        (6*(links B).card : ℕ) * (C * ‖t‖^(r+1)) := by
  obtain ⟨C,hC,h⟩ := FundedWilsonBackgroundTail.normalized G r
  refine ⟨C,hC,fun n U B hB t ht h₁ => ?_⟩
  rw [expansion,Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ faces B, ‖(t^2)⁻¹ *
        FundedWilsonBackgroundTail.remainder (r+2) (Quad.mat (base U i)) (t • directions B i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ faces B, C * ‖t‖^(r+1) :=
      Finset.sum_le_sum fun i _ => h (base U i) (directions B i) (hB i) t ht h₁
    _ = ((faces B).card : ℝ) * (C * ‖t‖^(r+1)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast incidence B) (by positivity)

end YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundAction
end
