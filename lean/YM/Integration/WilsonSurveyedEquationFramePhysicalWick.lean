import YM.Integration.WilsonSurveyedEquationFrameWick

/-! On the elected survey the actual Wick operator preserves the physical lift at
every horizon. A covariance on the lifted jets induces a covariance on the
Maxwell slots by substitution of the finite one-leg rows. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option warningAsError true
namespace YM.Integration.WilsonSurveyedEquationFramePhysicalWick
open Finset Finsupp Function MvPolynomial Labels Source Maxwell Maxwell.Free
open XSpace Next.Rank.Normal XSpace.Contraction
open WilsonSurveyedEquationFrameBasis (projection kernel)
open scoped Classical BigOperators
variable {G : Gauge} {H : Hol G} {d : ℕ}

def legs (a : Maxwell.Slot G) : Labels.Key G →₀ ℂ :=
  ∑i:Fin (Labels.dim G a.1), single ⟨a.1,i⟩
    ((coordinateLeg a (On.solve G a.1 (axes G a.1 i)) : ℝ) : ℂ)

private theorem source : exchange (legs (G:=G)) = On.lifting := by
  ext1 a
  rw [On.lifting,exchange_x,aeval_X,legs,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [glyph,linearCombination_single,MvPolynomial.C_mul']

theorem contracted (A : Survey G H d) (z : ℝ) (v : shellSector G d) :
    (A.insertW z (On.sectionMap d v)).val =
      On.lifting (milk (scope legs (A.selfCov z)) v.val) := by
  rw [Survey.insertW_val,On.section_value,←source,prepared]

theorem kept (A : Survey G H d) (z : ℝ) (v : shellSector G d) :
    projection (A.insertW z (On.sectionMap d v)) = A.insertW z (On.sectionMap d v) := by
  apply Subtype.ext
  change On.lifting (reduceEq (A.insertW z (On.sectionMap d v)).val) = (A.insertW z (On.sectionMap d v)).val
  rw [contracted,On.lift_recover]

theorem restored (A : Survey G H d) (z : ℝ) (p : Label G d) :
    projection (A.insertW z (projection p)) = A.insertW z (projection p) :=
  kept A z ((observable G d).rangeRestrict p)

private lemma pivot (p : Label G d) : projection (projection p) = projection p := by
  apply congrArg (On.sectionMap d)
  exact Subtype.ext (On.recovers _)

private lemma quiet (p : Label G d) : projection (kernel p) = 0 := by
  rw [kernel,LinearMap.sub_apply,LinearMap.id_apply,map_sub,pivot,sub_self]

/-- Wick-correct only the surveyed physical pivots and keep the actual equation
representatives of each remaining rank. -/
def retune (A : Survey G H d) (z : ℝ) : Module.End ℂ (Label G d) :=
  A.insertW z ∘ₗ projection + kernel

@[simp] theorem retune_formula (A : Survey G H d) (z : ℝ) (p : Label G d) :
    retune A z p = A.insertW z (projection p) + kernel p := rfl

private theorem retune_undo (A : Survey G H d) (z : ℝ) (p : Label G d) :
    retune A (-z) (retune A z p) = p := by
  have mark : kernel (retune A z p) = kernel p := by
    change retune A z p - projection (retune A z p) = kernel p
    rw [retune_formula,map_add,restored,quiet,add_zero,add_sub_cancel_left]
  rw [retune_formula,mark,retune_formula,map_add,restored,quiet,add_zero,A.wick_recovers]
  change projection p + (p - projection p) = p
  abel

def chart (A : Survey G H d) (z : ℝ) : Label G d ≃ₗ[ℂ] Label G d :=
  LinearEquiv.ofLinear (retune A z) (retune A (-z))
    (LinearMap.ext fun p => by simpa only [LinearMap.comp_apply,LinearMap.id_apply,neg_neg] using retune_undo A (-z) p)
    (LinearMap.ext fun p => retune_undo A z p)

theorem price (F : Frame G d) (A : Survey G H d) (z : ℝ) :
    ∃C : ℝ, 0 ≤ C ∧ ∀p : Label G d, ‖F.coords ((chart A z).symm p)‖ ≤ C * ‖F.coords p‖ := by
  let C := ((F.coords.symm.trans (chart A z).symm).trans F.coords).toLinearMap.toContinuousLinearMap
  refine ⟨‖C‖,norm_nonneg _,fun p => ?_⟩
  simpa [C] using C.le_opNorm (F.coords p)

end YM.Integration.WilsonSurveyedEquationFramePhysicalWick
