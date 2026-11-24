import YM.Integration.WilsonPositionProgramTrialMeasuredTangent
import YM.Integration.WilsonOriginalPublicPivotReflected

/-! The sampled reflected quadratic on the actual common inversion uses every
proper slot of the same issued vector. Its first source variation is a sum of
ground readings on this same board, with no loss in its inversion period. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialMatchedGram
open Finset Lattice RG Wilson Labels Source PhysicalNext.Repeat.Legato PowerSeries
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1
open Maxwell
open WilsonThermometerPositionTunedSlope (paid finite)
open WilsonPositionProgramTrialThermalGrades (frozen)
open WilsonOriginalPublicPivotReflected (board sampled evaluated)
open WilsonPositionProgramTrialMeasuredTangent (value move)
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (W : Initialize G) (d : Fin 2 → ℕ)
variable (v : (i : Fin 2) → (R.family.labels.level (d i)).Index → PowerSeries ℂ)

def issued (x : Sample 2) (s : Finset (Fin 2)) : PowerSeries ℂ :=
  paid R (d ∘ Subtype.val : s → ℕ) (fun j : s => v j.val)
    (finite R (d ∘ Subtype.val : s → ℕ) x.F.p (fun j : s => x.layout j) (W.tree x.F.p))

def variation (s : Finset (Fin 2)) : ℝ :=
  ∑ i : s, ∏ j : s, (R.family.labels.level (d j.val)).coeffSize
    (move R (d ∘ Subtype.val : s → ℕ) (fun j : s => v j.val) i j)

theorem ground (x : Sample 2) (s : Finset (Fin 2)) :
    coeff 0 (issued R W d v x s) = coeff 0 (board R W d (value R d v 0) x s) :=
  WilsonPositionProgramTrialMeasuredTangent.ground R _ _ _

theorem first (x : Sample 2) (s : Finset (Fin 2)) :
    coeff 1 (issued R W d v x s) = coeff 1 (board R W d (value R d v 0) x s) +
      ∑ i : s, coeff 0 (paid R (d ∘ Subtype.val : s → ℕ)
        (frozen R (d ∘ Subtype.val : s → ℕ)
          (move R (d ∘ Subtype.val : s → ℕ) (fun j : s => v j.val) i))
        (finite R (d ∘ Subtype.val : s → ℕ) x.F.p (fun j : s => x.layout j) (W.tree x.F.p))) :=
  WilsonPositionProgramTrialMeasuredTangent.first R _ _ _

theorem original (s : Finset (Fin 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : (i : Fin 2) → (R.family.labels.level (d i)).Index → PowerSeries ℂ) (x : Sample 2),
    ‖coeff 1 (issued R W d v x s) - coeff 1 (board R W d (value R d v 0) x s)‖ ≤
      C * variation R d v s := by
  let place : s → Fin 3 := fun i => i.val.castSucc
  obtain ⟨C,hC,read⟩ := WilsonPositionProgramTrialMeasuredTangent.original R (d ∘ Subtype.val : s → ℕ) place
  refine ⟨C,hC,fun v x => ?_⟩
  let sites : Fin 3 → Cover := Fin.lastCases 0 x.layout
  have where_ : sites ∘ place = fun i : s => x.layout i := by
    funext i
    simp [sites,place]
  have h := read (fun i : s => v i.val) sites x.F.p (W.tree x.F.p)
  rw [where_] at h
  exact h

end YM.Integration.WilsonPositionProgramTrialMatchedGram
