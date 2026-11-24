import YM.RGComparison.Core16.WilsonXLocal
import YM.Pert.Asymptotics.RawAxis

/-!
# Fixed-history evaluation: through a finite chain of true coupling resets

This low-order perturbative test runs to the final *conditional* readout at flat. Tail and other
costs on that domain contained in `Savings`. It exercises the same beta and budgets that a
full proof will have to use. Specialization to general finite history and O's; requires no
hypothesis predicting the resets because their influence in this reading starts later than this
first order. Expansion parameter g_N, sqrt inverse beta from the upper endpoint of the descent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16
open Lattice RG Tree Wilson Precision Push.BetaTransport Marker
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Descent WilsonXLocal
open Pert.Asymptotics (regulatorRun)
variable {G : Gauge} (C : Family G) (p N : ℕ) {m : ℕ}

/-- Actual offsets -- no reset interpretation used for coefficients. -/
def actualOffset (m i : ℕ) := C.path.β N p (m+i) - C.path.β N p N

/-- Local envelope paying offsets (explicit, no period cost and no inference that the calibrated
slope is an independently constructed perturbative coefficient). -/
def driftRoof (C : Family G) (i : ℕ) : ℝ := (C.path.levels.clock.params (i+1)).drift +
    |G.slopeConstant * Real.log (C.S.block i).val|

def resetBill (C : Family G) {N : ℕ} (m : ℕ) (h : m ≤ N) :=
    Nat.decreasingInduction (motive:=fun _ _ => ℝ) (fun i _ r => driftRoof C i + r) 0 h

variable {p N C} (h : C.Makes)

include h in
lemma line_offset : offset (actualOffset C p N m) (regulatorRun C N p N) = line C.path p m N := by
  funext i
  simp only [offset,regulatorRun,actualOffset,line, inv_inv, Real.sq_sqrt (Overlay.beta_positive h.wilson (le_rfl : N≤N)|>.le)]
  ring

include h in
lemma drift_guard (e : m < N) : ‖C.path.β N p (m+1) - C.path.β N p m‖ ≤ driftRoof C m := by
  let x := C.path.β N p (m+1) - C.path.β N p m
  let b := G.slopeConstant * Real.log (C.S.block m).val
  exact (le_of_eq (congr_arg _ (sub_add_cancel x b).symm)).trans ((norm_add_le ..).trans (add_le_add_left
    ((h.wilson.steps N p m e).2) _)) -- orientation add_le_

variable (Z : Slices C.path.levels p) (hm : m ≤ N)

include h in
lemma roof_guard : (traversal Z hm).Band (resetBill C m hm) (actualOffset C p N m) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    intro i hi; rw [traversal_depth] at hi
    have hz : resetBill C N (le_rfl: N ≤ N) = 0 := Nat.decreasingInduction_self ..
    simp [hz,actualOffset,show i=0 by omega]
  | of_succ m hm ih =>
    let B := resetBill C (m+1) (show m+1≤N from hm)
    have hx : resetBill C m hm.le = driftRoof C m + B := Nat.decreasingInduction_succ_left ..
    intro i hi
    rcases i with _|i
    · rw [hx]; apply le_trans (norm_sub_le_norm_sub_add_norm_sub (C.path.β N p m) (C.path.β N p (m+1)) (C.path.β N p N)) ?_
      rw [norm_sub_rev]
      apply add_le_add (drift_guard h hm) (ih 0 (Nat.zero_le _))
    have h₁ : i≤ (traversal Z hm).depth := by rw [traversal_depth] at hi ⊢; omega
    have h₂ : 0 ≤ driftRoof C m := add_nonneg (Stage.drift_ge _) (abs_nonneg _)
    rw [hx,actualOffset,show m+(i+1)=m+1+i by omega]
    exact (ih i h₁).trans (le_add_of_nonneg_left h₂)

variable {ι : Type} [DecidableEq ι] (O : ι → Config G (C.side N p) → ℂ) (K : Census ι)
    (w : ι → ℕ) (H : ∀ i, (traversal Z hm).Testable (O i))
    (hg : ∀ i, (traversal Z hm).grade (O i) (w i))
    (S : ChartRatio G) (R : LocalRatio S) (hR : (traversal Z hm).Room G)

include h H hg R hR
/-- Low-order endpoint, parameter/log costs as at this finite history (NOT transferring estimate
norms conditioned at other V). Same constants in the uniform in coupling bound at this geometry,
and in the specialization at the true physical value so this isn't just saying ∃C pointwise. The
second bound writes the readout on the actual constructed mass `(C.path.rep N p m).eval 1`. -/
theorem low_endpoint : ∃ A : ℝ, 0 ≤ A ∧ (∀ a : ℝ, 0 < a → ∀ u, (traversal Z hm).Band (resetBill C m hm) u → ∀ (T : K.Mode),
      ‖a⁻¹ ^ weight K w T • ((traversal Z hm).moments K (offset u a) O 1).part T -
        peval (conditionalTerms S O K w (traversal Z hm) 0 T) 1 a‖ ≤ A * a^2) ∧
      (let a := regulatorRun C N p N; 0 < a ∧ ∀ (T : K.Mode),
        ‖a⁻¹ ^ weight K w T •
            ( (((C.path.rep N p m).eval 1 : ℝ) : ℂ)⁻¹ * ((traversal Z hm).marks K (line C.path p m N) O 1).part T) -
            peval (conditionalTerms S O K w (traversal Z hm) 0 T) 1 a‖ ≤ A * a^2) := by
  let M := resetBill C m hm; have hp := roof_guard h Z hm
  have hM : 0 ≤ M := nonnegativeBand hp
  obtain ⟨A,E,hA,hE,U⟩ := every_moment S R 1 hR (v:=0) (M:=M) (fun i _ => by simp [hM]) O K w H hg
  let p' := regulatorRun C N p N
  have he : 0<p' := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive h.wilson (le_refl N)))
  have ht a (ha:0<a) u (hu : (traversal Z hm).Band M u) T := U a ha u M hu (by simpa using hu) T
  have hf a (ha:0<a) u (hu: (traversal Z hm).Band M u) T : ‖a⁻¹ ^ weight K w T • ((traversal Z hm).moments K (offset u a) O 1).part T - peval (conditionalTerms S O K w (traversal Z hm) 0 T) 1 a‖ ≤ (A+E*M) * a^2 := (ht a ha u hu T).trans_eq (by ring)
  refine ⟨A+E*M, by positivity,hf,he,fun i => ?_⟩
  let f := line C.path p m N
  have hx := hf _ he (actualOffset C p N m) hp i
  rw [Descent.conditional_mark, show offset _ p'= f from line_offset h, vacuum_eq Z h.wilson hm] at hx
  exact hx
end YM.RGComparison.Core16
