import YM.Integration.FVA1Physical.Wilson.InheritedReadout
import YM.RGComparison.Core16.Evaluation
import YM.Integration.RunFormalChain

/-! Prices for the actual selected run at any finite retained depth.
The bound controls the joint physical source readings with the full interacting
vacuum. Constants are selected after the finite torus and before the probing
coupling, perturbation of the clock and joint marker mode. -/

noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Lattice RG Wilson Tree Precision Marker RGComparison.Core16 RGComparison.Core16.Descent
open RGComparison.Core16.WilsonXLocal PertExtension.Series.Tested FormalOPE.RG10.InversionTop
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V]
    (R : Census V) (A : Run G) {N p m d : ℕ} (U : V → Stamp.Reservation A.family (A.family.side N p) d)
    (T : Slices A.family.path.levels p) (hm : m ≤ N)
    (H : (traversal T hm).Room G) (t : (traversal T hm).Tags)

/-- Perturb the inverse squared couplings along any finite physical chain.
The second summand pays the largest drift across the interior levels. -/
theorem perturbed_history_price (v : ℕ → ℝ) {M : ℝ} (hv : (traversal T hm).Band M v) (r : ℕ) :
    ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ g : ℝ, 0 < g → ∀ u δ,
      (traversal T hm).Band M u → (traversal T hm).Band δ (u-v) → ∀ s : R.Mode,
      ‖g⁻¹ ^ weight R (MSMatch.SourceTop.grade U) s •
          ((traversal T hm).moments R (offset u g) (MSMatch.SourceTop.field U) 1).part s -
        peval (historyCoefficient R U (traversal T hm) (RunFormalChain.fromRun A).O H t v s) r g‖ ≤
            B*g^(r+1) + E*g^2*δ := by
  let Z := RunFormalChain.fromRun A
  have hj (i : V) := basis_test A.makes (Next.Foundations.valuation G (U i).height)
    (traversal T hm) (U i).anchor (U i).leg
  obtain ⟨B,E,hB,hE,hh⟩ := every_moment Z.O Z.receipt r H hv (MSMatch.SourceTop.field U) R
    (MSMatch.SourceTop.grade U) (fun i => (hj i).1) (fun i => (hj i).2)
  refine ⟨B,E,hB,hE, ?_⟩
  intro g hg u δ h₁ h₂ s
  rw [← conditionalTerms_history R U (traversal T hm) Z.O H t v Z.receipt s]
  exact hh g hg u δ h₁ h₂ s

/-- At the measured offsets, the same independently evaluated solenoid
coefficients control all positive probe couplings, including the physical
bare coupling, with the true terminal vacuum of the run. -/
theorem calibrated_history_price (r : ℕ) :
    let v := actualOffset A.family p N m
    let D := traversal T hm
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ g : ℝ, 0 < g → ∀ s : R.Mode,
        ‖g⁻¹ ^ weight R (MSMatch.SourceTop.grade U) s •
          (D.moments R (offset v g) (MSMatch.SourceTop.field U) 1).part s -
          peval (historyCoefficient R U D (RunFormalChain.fromRun A).O H t v s) r g‖ ≤ B*g^(r+1)) ∧
      let g := regulatorRun A.family N p N
      0 < g ∧ ∀ s : R.Mode,
        ‖g⁻¹ ^ weight R (MSMatch.SourceTop.grade U) s •
          ((((A.family.path.rep N p m).eval 1 : ℝ) : ℂ)⁻¹ *
          (D.marks R (line A.family.path p m N) (MSMatch.SourceTop.field U) 1).part s) -
          peval (historyCoefficient R U D (RunFormalChain.fromRun A).O H t v s) r g‖ ≤ B*g^(r+1) := by
  dsimp only
  let v := actualOffset A.family p N m
  have hv := roof_guard A.makes T hm
  obtain ⟨B,E,hB,_,hh⟩ := perturbed_history_price R A U T hm H t v hv r
  have hap (g : ℝ) (hg : 0 < g) (s : R.Mode) := hh g hg v 0 hv
    (show (traversal T hm).Band 0 (v-v) from fun _ _ => by simp) s
  simp only [mul_zero, add_zero] at hap
  let g := regulatorRun A.family N p N
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive A.makes.wilson (le_refl N)))
  refine ⟨B,hB,hap,hg,fun s => ?_⟩
  have hs := hap g hg s
  rw [show offset v g = line A.family.path p m N from line_offset A.makes,
    conditional_mark,vacuum_eq T A.makes.wilson hm] at hs
  exact hs

end YM.Integration.FVA1Physical.Wilson

