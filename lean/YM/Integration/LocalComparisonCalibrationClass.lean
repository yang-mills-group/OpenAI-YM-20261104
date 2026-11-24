import YM.RG.History

/-!
# Local presentation of the optional qlocal calibration input

This is the per-datum input class for the manuscript's designated `eta_w)
calibration. The outer qlocal statement supplies its actual winding/correction
schedule and uniform smallness against every fixed coupling power.

The original full-field term and its regular germ are both retained. Their
difference includes clipping corrections, while the difference between the
germ and its masked value includes the complete failed-mask correction.
Native exponential hit budgets control the countable presentation; finite
presentations are included by zero padding. Full-group bounds apply before
discarding either correction. No affine-nullness is imposed on these terms.

The containing fine-input record must identify `amount` in the exact original
vacuum exponent. This class does not construct that identification, perform
scalar/kinetic reset, purchase a forced divisor, or bound an arbitrary extensive
perturbation. All seed statements below refer to the same original gas of Q.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FullQLocal

open Lattice Wilson RG MeasureTheory
open scoped BigOperators Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

/-- Complete local data for the designated calibration term. The supports in
`original_reads` include every selector/path/clip query; `UsesFinal` retains
the native inspected support for actual flag reads. -/
structure CalibrationPresentation (Q : RG.Rep G n) (p : BudgetPoint)
    (eta_w : ℝ) where
  threshold : p.threshold = Q.p.threshold
  size_nonnegative : 0 ≤ eta_w
  address : ℕ → RegularAddress n
  original : ℕ → Config G n → ℝ
  germ : ℕ → Config G n → ℝ
  regular : ∀ i, p.Regular (address i).support (germ i)
  original_measurable : ∀ i, Measurable (original i)
  original_gauge : ∀ i, GaugeInvariant (original i)
  original_reads : ∀ i, UsesFinal Q.p.threshold (address i).support (original i)
  on_healthy : ∀ i U, Healthy Q.p.threshold (address i).support U →
    original i U = germ i U
  regularMajorant : ℕ → ℝ
  fullMajorant : ℕ → ℝ
  regular_bound : ∀ i,
    p.supBounds (address i).site (address i).support (germ i) (regularMajorant i)
  full_nonnegative : ∀ i, 0 ≤ fullMajorant i
  original_bound : ∀ i U, ‖original i U‖ ≤ fullMajorant i
  germ_bound : ∀ i U, ‖germ i U‖ ≤ fullMajorant i
  regular_total : ∀ x : Site n, SumBudget
    (fun i => if (address i).site = x then
      p.mass (address i).support (regularMajorant i) else 0) eta_w
  full_hit : ∀ x : Site n, SumBudget
    (fun i => if x ∈ (address i).support then
      p.mass (address i).support (fullMajorant i) else 0) eta_w

namespace CalibrationPresentation

variable {Q : RG.Rep G n} {p : BudgetPoint} {eta_w : ℝ}
variable (C : CalibrationPresentation Q p eta_w)

def regularTerm (i : ℕ) : Config G n → ℝ :=
  masked Q.p.threshold (C.address i).support (C.germ i)

/-- Full clipping difference, before the regular mask is applied. -/
def clipFailure (i : ℕ) (U : Config G n) : ℝ :=
  C.original i U - C.germ i U

/-- Complete failure of the original regular mask. -/
def maskFailure (i : ℕ) (U : Config G n) : ℝ :=
  C.germ i U - C.regularTerm i U

def failed (i : ℕ) (U : Config G n) : ℝ :=
  C.original i U - C.regularTerm i U

def partner (i : ℕ) (U : Config G n) : ℝ :=
  Real.exp (-C.failed i U) - 1

def amount (U : Config G n) : ℝ := ∑' i, C.original i U

def regularAmount (U : Config G n) : ℝ := ∑' i, C.regularTerm i U

def failedAmount (U : Config G n) : ℝ := ∑' i, C.failed i U

private theorem majorant_summable : Summable C.fullMajorant :=
  Activities.summable_charge
    (fun i => ⟨(C.address i).site, (C.address i).anchor⟩)
    C.full_nonnegative C.full_hit

private theorem original_summable (U : Config G n) :
    Summable (fun i => C.original i U) :=
  (show Dominated C.original from
    ⟨C.fullMajorant, C.majorant_summable, C.original_bound⟩).summable U

private theorem regular_summable (U : Config G n) :
    Summable (fun i => C.regularTerm i U) := by
  apply (show Dominated C.regularTerm from ?_).summable U
  refine ⟨C.fullMajorant, C.majorant_summable, ?_⟩
  intro i V
  by_cases h : Healthy Q.p.threshold (C.address i).support V
  · rw [regularTerm, masked_eq _ _ _ _ h]
    exact C.germ_bound i V
  · rw [regularTerm, masked_ne _ _ _ _ h, norm_zero]
    exact C.full_nonnegative i

theorem failed_split (i : ℕ) (U : Config G n) :
    C.failed i U = C.clipFailure i U + C.maskFailure i U := by
  dsimp only [failed, clipFailure, maskFailure]
  ring

theorem failed_zero (i : ℕ) (U : Config G n)
    (h : Healthy Q.p.threshold (C.address i).support U) :
    C.failed i U = 0 := by
  rw [failed, C.on_healthy i U h, regularTerm, masked_eq _ _ _ _ h, sub_self]

theorem partner_zero (i : ℕ) (U : Config G n)
    (h : Healthy Q.p.threshold (C.address i).support U) :
    C.partner i U = 0 := by
  rw [partner, C.failed_zero i U h]
  norm_num

/-- A nonzero correction in a nonzero original gas occurrence meets an actual
selected forced inventory. Its coefficient is also nonzero; no synthetic flag
or replacement gas law is used. -/
theorem partner_seed (i : ℕ) (U : Config G n) (b : Finset ℕ)
    (hpartner : C.partner i U ≠ 0)
    (hgas : Q.activities.gasOccurrence Q.p b U ≠ 0) :
    ∃ j ∈ b, ∃ x ∈ (C.address i).support,
      x ∈ (Q.activities.forced j).inventory ∧
      x ∈ flags Q.p.threshold U ∧ Q.activities.K j U ≠ 0 := by
  classical
  have had : Q.activities.admissible Q.p U b := by
    by_contra h
    exact hgas (by simp only [Activities.gasOccurrence, if_neg h])
  have hbad : ¬ Healthy Q.p.threshold (C.address i).support U :=
    fun h => hpartner (C.partner_zero i U h)
  have hx : ∃ x ∈ (C.address i).support, x ∈ flags Q.p.threshold U := by
    by_contra h
    apply hbad
    exact Finset.disjoint_left.mpr fun x hs hf => h ⟨x, hs, hf⟩
  obtain ⟨x, hs, hf⟩ := hx
  have hc : x ∈ b.biUnion (fun j => (Q.activities.forced j).inventory) := by
    rwa [had.2]
  obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hc
  have hp : (∏ k ∈ b, Q.activities.K k U) ≠ 0 := by
    simpa only [Activities.gasOccurrence, if_pos had] using hgas
  exact ⟨j, hj, x, hs, hxj, hf, (Finset.prod_ne_zero_iff.mp hp) j hj⟩

/-- Exact single-term identity, including both clipping and mask failures. -/
theorem occurrence_reexpression (i : ℕ) (U : Config G n) (b : Finset ℕ) :
    Real.exp (-C.original i U) * Q.activities.gasOccurrence Q.p b U =
      Real.exp (-C.regularTerm i U) * (1 + C.partner i U) *
        Q.activities.gasOccurrence Q.p b U := by
  have h : C.original i U = C.regularTerm i U + C.failed i U := by
    dsimp only [failed]
    ring
  rw [h, neg_add, Real.exp_add]
  dsimp only [partner]
  ring

theorem amount_split (U : Config G n) :
    C.amount U = C.regularAmount U + C.failedAmount U := by
  change (∑' i, C.original i U) =
    (∑' i, C.regularTerm i U) + ∑' i, (C.original i U - C.regularTerm i U)
  rw [(C.original_summable U).tsum_sub (C.regular_summable U)]
  ring

/-- Full-field identity for the unchanged original gas. It is not a claim that
the exponential correction has already been rebooked into a new Valid gas. -/
theorem gas_reexpression (U : Config G n) :
    Real.exp (-C.amount U) * Q.activities.gas Q.p U =
      Real.exp (-C.regularAmount U) *
        (Real.exp (-C.failedAmount U) * Q.activities.gas Q.p U) := by
  rw [C.amount_split U, neg_add, Real.exp_add]
  ring

end CalibrationPresentation
end YM.Integration.FullQLocal
end
