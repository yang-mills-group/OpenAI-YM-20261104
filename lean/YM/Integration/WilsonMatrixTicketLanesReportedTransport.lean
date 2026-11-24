import YM.Integration.WilsonMatrixTicketLanesReportedAdmission
import YM.Integration.WilsonFundedMeasuredWindow
import YM.SharpGram.Weak.Bill

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedTransport
open Function Filter Real OPE RG12 RG17 Extraction Spec Wilson Table RG Lattice
open SharpGram Next.UVStress PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F) (E : Services R.family f S)

include E in
/-- The normalized original upper charge at every earlier date is bounded by its
actual paid reporting charge. Both entries refer to the same operator and period. -/
theorem earlier (d : ℕ) (r : ℝ) (w : R.family.label d) (s N p : ℕ)
    (hr : R.family.ref d ≤ s) (hs : s ≤ L.level r) (hn : L.level r ≤ N) :
    quota R.family d s N p (atRef L d r (N,p) w) / R.family.S.a s^d ≤
      mass R.family d (L.shift d r w) := by
  obtain ⟨W,c,D,tickets⟩ := E.purchase
  have price := SharpGram.passPrice (p:=p) tickets.toTableTickets (atRef L d r (N,p) w) hr hs hn
  rw [WilsonMatrixTicketLanesReportedAdmission.quota R F L d r w (hr.trans hs) N p hn] at price
  apply (div_le_iff₀ (pow_pos (R.family.S.a_pos _) _)).2
  refine price.trans_eq ?_
  rw [div_pow]
  field_simp [(R.family.S.a_pos s).ne', (R.family.S.a_pos (L.level r)).ne']

include E in
/-- At a finer intermediate date the incurred cost is exactly one mesh-ratio factor
for the transport and (d) more for the engineering normalization. -/
theorem later (d : ℕ) (r : ℝ) (w : R.family.label d) (s N p : ℕ)
    (hr : R.family.ref d ≤ L.level r) (hs : L.level r ≤ s) (hn : s ≤ N) :
    quota R.family d s N p (atRef L d r (N,p) w) / R.family.S.a s^d ≤
      (R.family.S.a (L.level r) / R.family.S.a s)^(d+1) * mass R.family d (L.shift d r w) := by
  obtain ⟨W,c,D,tickets⟩ := E.purchase
  have price := SharpGram.Weak.Portfolio.reverseWalk (p:=p) (H:=R.makes) tickets.toTableTickets
    (atRef L d r (N,p) w) hr hs hn
  change quota R.family d s N p (atRef L d r (N,p) w) ≤
    R.family.S.a (L.level r) / R.family.S.a s *
      quota R.family d (L.level r) N p (atRef L d r (N,p) w) at price
  rw [WilsonMatrixTicketLanesReportedAdmission.quota R F L d r w hr N p (hs.trans hn)] at price
  apply (div_le_iff₀ (pow_pos (R.family.S.a_pos _) _)).2
  refine price.trans_eq ?_
  rw [div_pow,pow_succ,pow_succ]
  field_simp [(R.family.S.a_pos s).ne', (R.family.S.a_pos (L.level r)).ne']

/-- The true thermal scale can grow by at most a fixed multiplicative factor in
one paid original block, uniformly in the date. -/
theorem temperature (pace : WilsonWindowReportingPace.Slow R.kit) (simple : G.Simple) (i h : ℕ) :
    R.family.path.levels.clock.hatBeta (i+h) ≤
      (1+G.slopeConstant)^h * R.family.path.levels.clock.hatBeta i := by
  let B := R.family.path.levels.clock.hatBeta
  have nonneg := (Gauge.slopeConstant_pos simple).le
  have step (k : ℕ) : B (k+1) ≤ (1+G.slopeConstant) * B k := by
    have source : ((R.family.S.block k).val:ℝ) ≤ Real.log (B k) :=
      WilsonFundedMeasuredWindow.paced R pace k
    have debit : Real.log ((R.family.S.block k).val:ℝ) ≤ B k :=
      (Real.log_le_self (Nat.cast_nonneg _)).trans (source.trans
        (Real.log_le_self (zero_lt_one.trans (R.family.path.levels.fits.delayed k)).le))
    have line : B (k+1) = B k + G.slopeConstant * Real.log ((R.family.S.block k).val:ℝ) := by
      unfold B Calendar.hatBeta
      rw [Schedule.scale_succ]
      ring
    rw [line,add_mul,one_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left debit nonneg)
  induction h with
  | zero => simp
  | succ h ih =>
    calc
      _ ≤ (1+G.slopeConstant) * B (i+h) := step _
      _ ≤ (1+G.slopeConstant) * ((1+G.slopeConstant)^h * B i) :=
        mul_le_mul_of_nonneg_left ih (add_nonneg zero_le_one nonneg)
      _ = _ := by rw [pow_succ]; ring

include E in
/-- Use the actual earlier clock to fund the same upper operator on a true finite
window ending at the reporting date. The price is uniform in the future N and p. -/
theorem interval (pace : WilsonWindowReportingPace.Slow R.kit) (simple : G.Simple)
    (d : ℕ) (r : ℝ) (w : R.family.label d) (s h e N p : ℕ)
    (hr : R.family.ref d ≤ s) (endAt : L.level r = s+h) (hn : L.level r ≤ N)
    (C : ℝ) (zero : 0 ≤ C)
    (fund : mass R.family d (L.shift d r w) ≤ R.family.path.levels.clock.hatBeta (L.level r)^e * C) :
    quota R.family d s N p (atRef L d r (N,p) w) / R.family.S.a s^d ≤
      ((1+G.slopeConstant)^h * R.family.path.levels.clock.hatBeta s)^e * C := by
  have order : s ≤ L.level r := endAt ▸ Nat.le_add_right s h
  refine (earlier R F L E d r w s N p hr order hn).trans (fund.trans ?_)
  apply mul_le_mul_of_nonneg_right _ zero
  rw [endAt]
  exact pow_le_pow_left₀ (zero_lt_one.trans (R.family.path.levels.fits.delayed _)).le
    (temperature R pace simple s h) _

end YM.Integration.WilsonMatrixTicketLanesReportedTransport
