import YM.Push.PRICE_COMPILER.Canonical
import YM.UVNext.PRICED_KERNELS.Bridge


-- Stylistic lint is not part of kernel or axiom acceptance.
set_option warningAsError false

-- Stylistic lint is not part of kernel or axiom acceptance.
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Kernel prices fixed before the block lengths

`issue` first fixes the linear kernel and then chooses the openings,
amounts, loop prices and final parameters in that order. `Built` gives
admissible block ratios and post-ratio preparations with the requested
bounds. Its horizons retain the chosen linear kernels, including at
same-stage edges. Nonlinear estimates require their own bounds on
these choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Pressure
open Push.PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

/-- Cap the direct price by both 1/2 and γ. Keep the linear price below one thirty-second of the new direct price. Positivity holds for each clip separately. -/
def cap (p : Clip) (γ : ℝ) (h : 0 < γ) : Clip where
  direct := min (min p.direct (1/2)) γ
  linear := min p.linear (min (min p.direct (1/2)) γ / 32)
  relaxation := p.relaxation
  quadratic_pos := lt_min (lt_min p.quadratic_pos (by norm_num)) h
  tail_pos := lt_min p.tail_pos (div_pos (lt_min (lt_min p.quadratic_pos (by norm_num)) h) (by norm_num))
  kink := lt_of_le_of_lt (min_le_right ..) (by
    have hx : 0 < min (min p.direct (1/2)) γ := lt_min (lt_min p.quadratic_pos (by norm_num)) h
    linarith)
  radius_pos := p.radius_pos



/-- Opening widths and row amounts are quoted on the canonical kernel. Loop prices depend on both, and the final parameters can depend on all three. These choices precede the block lengths. -/
structure EndNumbers where
  relaxation : ℕ → ℝ
  reserve : HaloBill
  lead : ℕ → ℝ
  columns : ℕ → ℝ

structure Charges where
  wants : (ℕ → Clip) → FlatBill → MapPrices → Openings
  asks : (ℕ → Clip) → FlatBill → MapPrices → Openings → Amounts -- choose for installed Openings including width change
  loops : (ℕ → Clip) → FlatBill → MapPrices → Openings → Amounts → LoopPrices
  late : (ℕ → Clip) → FlatBill → MapPrices → Openings → Amounts → LoopPrices → EndNumbers



def issue (G : Gauge) (p : Before) (Q : FlatBill)
    (c : ℕ → Clip) (R : Charges) : Before :=
  let K := preMap (p.kernelChoice G) c Q G
  let w := Canonical.orderWidth K (R.wants c Q K)
  let a := Canonical.orderRows K (R.asks c Q K w)
  let o := R.loops c Q K w a
  let f := R.late c Q K w a o
  { p with
    clip := c, flat := Q, opening := w, amount := a,
    slopePrices := o,relaxation:=f.relaxation,reserve:=f.reserve,lead:=f.lead,columns:=f.columns }



lemma linear_paths (G : Gauge) (p : Before) (Q : FlatBill) (c : ℕ → Clip) (R : Charges) :
    let P := issue G p Q c R
    let K := preMap (p.kernelChoice G) c Q G
    let w := R.wants c Q K
    let a := R.asks c Q K P.opening
    Canonical.Quotes (P.frozen G) P.opening P.amount ∧ P.opening.wish ≤ w.wish ∧
      a.born ≤ P.amount.born ∧ a.sends ≤ P.amount.sends := by
  intro P K w a
  obtain ⟨ht,hs,hq⟩ := Canonical.orderRows_quotes K w a
  exact ⟨hq,Canonical.orderWidth_le K w,ht,hs⟩

/-- A stock of Direct choices after knowing γ (no need to rewrite linear if
already planning it on the actual smaller direct). -/
structure Caps (first : ℕ) (γ : ℕ → ℝ) where
  clips : ℕ → Clip
  meets i : first ≤ i → (clips i).direct ≤ γ i



section Issuance
variable (P : Before) (X : MapPrices) (l : ℕ → ℝ)

/-- End-to-end quantitative schedules here, a reusable interface for *augmenting*
the various floors/delays at these orders. Also read local consumers/single
`wire` lemma to add to any other scheduling cuts if proving `Permit` there.
No universal or even on-this-schedule nonlinear estimates yet.
-/
structure Built (G : Gauge) (P : Before) (X : MapPrices) (l : ℕ → ℝ) (g : ℕ → ℕ) : Prop where
  pre : Before.Funded P G g
  nonempty : Nonempty (Rolls (P.sheet G g))
  post (D : Rolls (P.sheet G g)) (w : ℕ → ℕ → ℝ) (η : ℕ → ℝ) : (∀ i, 0 < η i) →
      ∃ M : Preparations P D, w ≤ M.w ∧ M.gap ≤ η ∧
        ∀ (q : AfterBill) (s : PostCost D → ℕ → ℝ), (∀ i, 0 < s (M.budget q) i) →
        ∃ T : Protection D, T.theta ≤ s (M.budget q) ∧ ∀ V : Delays T,
          ∃ W : Delays T, OrderedDelays W ∧ DelayLe V W ∧ ∀ U : Delays T, DelayLe W U →
            M.Ledger U ∧ ∀ β : ℝ, ∃ Y : Bar U, β ≤ Y.value ∧ Nonempty (Wait Y) ∧
              ∀ I : Wait Y, ∃ a : Levels G, Permit M I a
  receives {D : Rolls (P.sheet G g)} {M : Preparations P D} {T : Protection D} {W : Delays T}
    {Y : Bar W} {I : Wait Y} {a : Levels G} : Permit M I a → ∃ B V : Horizon a, Wired P a X l B V





end Issuance
end YM.UVNext.PricedKernels
