import YM.Integration.FVA1Physical.MixedResets.Rooted
import YM.QuadraticLocal.Campaign.Reach
import YM.QuadraticLocal.Display

/-!
# Full budget on the represented *difference*, regular, marked and forced

The comparison uses the norm of the specified representation. The Gallery of the difference
retains the entire forced ledger (model marks compared in connected *regular*
coefficients, all its forced partners estimated at output). Control before
every evaluation. This is for multiple marks, not the Gear of the one-mark
step where one asks in addition for `π^natural`-null readouts and contracts the
marks. The numerical marked rate for multiple marks does not use such contraction or first
split a projection. The readout works even if an output retains a globally
observable scalar at a nonquiet mode. Disconnected identity AND price for
regular-factor error on the connected representation (no connected price asserted
on a disconnected product).

Rooted conversion is on this very packet (no reclosure). Also provide an
accessor for the alternative `LocalComparison.FullBudget` currency using the
pre-existing *layout-preserving* `Display` adapter on the same Gallery.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Function Filter Finset Lattice RG Wilson Marker Ac
open QuadraticLocal QuadraticLocal.Earn
open Push.Corrected Push.AbsoluteSums MeasureTheory
open Integration.LocalComparison
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {V ι μ X : Type} [Fintype V] [DecidableEq V]
    {I : Marker.Census V} {o : Passport n V} (P : Rep G n)
    (w : V → ℝ) (κ : ℝ) (M : ι → Row o I G X) (U : Tint.Incoming o P X μ I)

def remainderGallery : QuadraticLocal.Gallery X μ o.origin P I := ⟨U.old, U.hard⟩

set_option quotPrecheck false
local notation "B" => P.p
local notation "Ψ" => remainderGallery P U

variable (reserve reg fee : ℝ)

/-- Norm control on this complete representation of a discrepancy. `κ` fixed by the actual run,
at a transition with `P` either the pre-reset rep or the calibrated next rep. -/
structure Full : Prop where
  divisor : 0 < κ
  positive i : 0 < w i
  regular : U.old.Paid w P.p.B (P.p.supportExponent+reserve) reg
  forced : U.hard.Paid w P.p.B P.p.supportExponent (fee*κ)

open GridRenewal.Rain
namespace Full
variable {P w κ U reserve reg fee} (h : Full P w κ U reserve reg fee)
include h

/-- Original per-marker norm. In particular apply it with two (or more) prescribed
markers held at ANY admitted separation. -/
lemma rooted : Rooted Ψ w κ reserve (3*reg) fee :=
  hit_rooted Ψ w κ reserve h.regular h.forced h.divisor h.positive

omit [Fintype V] in
lemma enlarge {e δ} (he : reg ≤ e) (hd : fee ≤ δ) : Full P w κ U reserve e δ :=
  ⟨h.divisor,h.positive,Lamps.loan_monotone _ h.regular he,Hard.mono _ h.forced
    (mul_le_mul_of_nonneg_right hd h.divisor.le)⟩
variable (hr : 0 ≤ reserve) (g : ℝ) (total : ℝ)
include hr

omit [Fintype V] in
lemma residual_pays : (remainderGallery P U).Pays w P.p.supportExponent reg (fee*κ) :=
  ⟨Lamps.tenure _ _ h.positive h.regular (le_add_of_nonneg_right hr), h.forced⟩

local notation "model" => (rendered M P.p g)

/-- Keep the report parameter `g`, before or after the true clock reset. The log discrepancy is
added *behind* the regular masks. -/
theorem reads (whole : (Tint.Patrol.report M U g).E.Paid w P.p.B P.p.supportExponent total)
    (x : X) (K : Config G n) :
    let a := (model).log x K
    let R := remainderGallery P U
    let W := Tint.Patrol.report M U g
    R.K=W.K ∧ W.E.log x K = a + U.old.log x K ∧
      W.density x K = Poly.pass a * R.density x K ∧ (W.density x K).part I.quiet= P.eval K ∧
      Summable (fun i => U.old.frame i x K) ∧
      Summable (fun i => (model).frame i x K) ∧
      Summable (Fusion.Attached.packet P.activities P.p (U.hard.hard x) K) := by
  let paid := h.residual_pays hr
  let terms := (model).inlPaid w U.old whole
  have hM := terms.sums P.p.exponent_pos.le h.positive x K
  have hE := paid.budget.sums P.p.exponent_pos.le h.positive x K
  intro a R W
  let b := R.E.log x K
  have hm : a.part I.quiet=0 := Lamps.quiet_of_hasSum x K hM
  have hb : b.part I.quiet=0 := Lamps.quiet_of_hasSum x K hE
  have ht : W.E.log x K = a+b := Lamps.joinLog x K hM hE
  refine ⟨rfl,ht, ?_, (Tint.Patrol.report M U g).same (QuadraticLocal.Gallery.Pays.mk whole h.forced) P.p.exponent_pos.le h.positive x K,hE,hM,?_⟩
  · change (↑(Real.exp _) : ℂ) • (Poly.pass (W.E.log x K) * R.gas x K)= _
    rw [ht, ← GridRenewal.Rain.passes (a+b) (by rw [Poly.part_plus,hm,hb,add_zero]), GridRenewal.Rain.plus,
      GridRenewal.Rain.passes a hm, GridRenewal.Rain.passes b hb]
    unfold Gallery.density; rw [mul_assoc, ← mul_smul_comm]
  · exact Hard.packet_summing U.hard h.forced P.p.exponent_pos.le h.positive x K

variable [Nonempty V][Countable μ][Nonempty X]
lemma viewpoint (hh : P.activities.ForcedFamily P.p) :
    Nonempty (Integration.LocalComparison.FullBudget (B) (Display.taste Ψ) w κ (4*reg) fee) ∧
    (∀ t U, Overlay.Bands.cluster (((Display.taste Ψ).leaf t).contents) U=(Ψ).gas t U) ∧
    (∀ t U,((Display.taste Ψ).leaf t).log U=(Ψ).E.log t U) ∧
    ∀ t, ((Display.taste Ψ).leaf t).density=(Ψ).density t :=
  Display.present Ψ hh h.positive le_rfl h.divisor (h.residual_pays hr)
end Full
end YM.Integration.FVA1Physical.MixedResets
