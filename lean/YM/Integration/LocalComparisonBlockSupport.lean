import YM.Integration.LocalComparisonBlockEnvelope
import YM.Integration.LocalComparisonInput
import YM.Next.RANK.Exponential

/-! Literal block support through the actual local transition.

This concerns the complete evaluated polynomial. It does not infer support
of each coefficient in an arbitrary re-expression from equality of full
densities, and therefore is not by itself a weighted-norm change of currency.
The input's forced remainder must retain the indicated block support too.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic LocalKernelBlocks
open scoped BigOperators Classical

variable {I V : Type} [DecidableEq I] [DecidableEq V] [Fintype V]
    (B : Layout I V) {R : Census V} {G : Gauge} {c f : Side}

omit [Fintype V] in
/-- The literal push at its stated beta preserves block support. The
nonintegrable case is the integral's zero value; this theorem does not claim
that an arbitrary input is integrable. -/
theorem push_block_supported (S : StepData c f) (beta : ℝ)
    (F : Config G f → Poly R) (hF : ∀ U, B.Supported (F U))
    (U : Config G c) : B.Supported (S.push beta F U) := by
  unfold StepData.push
  by_cases h : Integrable (fun V : Config G f => S.density beta V U • F V) (prior G f)
  · intro q hq
    change (Poly.get q) (∫ V : Config G f, S.density beta V U • F V ∂(prior G f)) = 0
    rw [← (Poly.get q).integral_comp_comm h]
    have hz : (fun V : Config G f => (Poly.get q) (S.density beta V U • F V)) =
        fun _ => 0 := by
      funext V
      change S.density beta V U • (F V).part q = 0
      rw [hF V q hq, smul_zero]
    rw [hz, integral_zero]
  · rw [integral_undef h]
    exact B.supported_zero

variable {C : YM.Family G} {N period level : ℕ}

theorem actualPush_block_supported
    (F : Config G (C.side (level + 1) period) → Poly R)
    (hF : ∀ U, B.Supported (F U)) (U : Config G (C.side level period)) :
    B.Supported (actualPush C N period level F U) :=
  push_block_supported B _ _ F hF U

theorem ExactStep.block_supported {X : Type*}
    {Q : Carrier C N period (level + 1)} {Q' : Carrier C N period level}
    {o : V → Site (C.side (level + 1) period)}
    {o' : V → Site (C.side level period)}
    {input : Taste X o Q.rep R} {output : Taste X o' Q'.rep R}
    (H : ExactStep Q Q' o o' input output)
    (h : ∀ x U, B.Supported ((input.leaf x).density U))
    (x : X) (U : Config G (C.side level period)) :
    B.Supported ((output.leaf x).density U) := by
  rw [← congr_fun (H.density x) U]
  exact actualPush_block_supported B _ (h x) U

variable {D : V → ComparisonDensity.Address.Orbit} {n : Side}

/-- Every literal packet keeps the complete input block named by its mode.
The countable-sum support statement does not replace the separate physical
summability receipt in `PrescribedPackets`. -/
theorem MarkedPackets.block_supported (P : MarkedPackets D G n R)
    (h : ∀ i T, P.packet i = some T → B.Admissible (P.mode i).val)
    (x : TestSpace D) (g : ℝ) (U : Config G n) :
    B.Supported (P.read x g U) := by
  unfold MarkedPackets.read
  apply B.supported_tsum
  intro i
  cases hp : P.packet i with
  | none => simpa only [MarkedPackets.term, hp, Poly.send_zero] using B.supported_zero (R := R)
  | some T => exact B.supported_send (P.mode i) (h i T hp) _

/-- Quiet packet coefficients vanish for the literal full rendering,
including its higher completion orders. -/
theorem MarkedPackets.quiet_read (P : MarkedPackets D G n R)
    (x : TestSpace D) (g : ℝ) (U : Config G n) :
    (P.read x g U).part R.quiet = 0 := by
  unfold MarkedPackets.read
  by_cases h : Summable (fun i => Poly.send (P.mode i) (P.term x g U i))
  · rw [Poly.share h]
    calc
      _ = ∑' _ : ℕ, (0 : ℂ) := tsum_congr (by
        intro i
        cases hp : P.packet i with
        | none => simp only [MarkedPackets.term, hp, Poly.send_zero, Poly.part_nil]
        | some T => rw [Poly.part_send, if_neg (Ne.symm (P.marked i T hp))])
      _ = 0 := tsum_zero
  · rw [tsum_eq_zero_of_not_summable h]
    rfl

theorem PreparedInput.block_supported
    {Q : Carrier C N period level} {roots : V → Site (C.side level period)}
    {input : Taste (TestSpace D) roots Q.rep R}
    {colors : TestSpace D → Comparison.RG02.Bulk.Colors R G (C.side level period)}
    {packets : MarkedPackets D G (C.side level period) R}
    {w : V → ℝ} {cost : R.Mode → ℝ} {forcedPrice : ℝ}
    (H : PreparedInput N period level Q roots input colors packets w cost forcedPrice)
    (hPackets : ∀ i T, packets.packet i = some T → B.Admissible (packets.mode i).val)
    (hRemainder : ∀ x U, B.Supported ((H.remainder.leaf x).density U))
    (x : TestSpace D) (U : Config G (C.side level period)) :
    B.Supported ((input.leaf x).density U) := by
  rw [H.full]
  exact B.supported_mul
    (B.supported_pass (MarkedPackets.block_supported B packets hPackets x _ U)) (hRemainder x U)

/-- Re-encode original analytic-input block envelopes at one actual slot
per block. The prepared input, its physical density, its colors and its
forced remainder all stay literally the same. -/
def PreparedInput.withSlotEnvelopes [Fintype I]
    {Q : Carrier C N period level} {roots : V → Site (C.side level period)}
    {input : Taste (TestSpace D) roots Q.rep R}
    {colors : TestSpace D → Comparison.RG02.Bulk.Colors R G (C.side level period)}
    {packets : MarkedPackets D G (C.side level period) R}
    {w : V → ℝ} {cost : I → ℝ} {forcedPrice : ℝ}
    (H : PreparedInput N period level Q roots input colors packets w
      (fun q => B.blockEnvelope cost q.val) forcedPrice)
    (hBlocks : BlockPresentation B H.remainder) (hc : ∀ i, 0 < cost i) :
    PreparedInput N period level Q roots input colors packets w
      (envelopeProduct (B.slotCost cost)) forcedPrice where
  convention := H.convention
  remainder := H.remainder
  regular_zero := H.regular_zero
  unit_zero := H.unit_zero
  caption_zero := H.caption_zero
  full := H.full
  forced_price := RelativeBudget.block_to_slots B H.forced_price
    (BlockPresentation.pullback B hBlocks (testInclusion D)) hc

/-- Algebraic removal of the same quiet-free model preserves full-polynomial
block support. No statement about individual re-expression labels follows. -/
theorem factor_block_supported {F M E : Poly R}
    (hF : B.Supported F) (hM : B.Supported M) (h0 : M.part R.quiet = 0)
    (he : F = Poly.pass M * E) : B.Supported E := by
  have h : Poly.pass (-M) * F = E := by
    rw [he, ← mul_assoc, Next.Rank.Exponential.pass_neg M h0, one_mul]
  rw [← h]
  exact B.supported_mul (B.supported_pass (B.supported_neg hM)) hF

end YM.Integration.LocalComparison
