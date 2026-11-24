import YM.Integration.WilsonOriginalTwoPrintedRows
import YM.Integration.WilsonEmittedLengthWindow
import YM.Integration.WilsonEmittedOutputPower

/-! One physical binder-length cutoff pays both the whole unmasked tail and
the ordered angular remainder on each freshly charged compact program. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrintedLength
open Finset Lattice Marker RG QuadraticLocal QuadraticLocal.Earn Push.AbsoluteSums
open WilsonEmittedGroupWallet WilsonEmittedRootSalary WilsonEmittedFiledCatalogue
open scoped BigOperators

private theorem payment {θ C b a u:ℝ}(pos:0<θ)(cp:0 ≤ C)(bp:0 ≤ b)(P W j:ℕ):
    0 ≤ Footprint.payment P W j θ C b a u:=by
  unfold Footprint.payment Footprint.degreeIncome
  have gap:0 ≤ 1-Real.exp (-θ):=sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  positivity

variable {A V:Type}[Fintype A][DecidableEq V] {Γ:Census V}
variable (s:Γ.Mode)(w:A→V→ℝ)(c:A→ℝ)(ℓ ν:A→ℕ)(B:BudgetPoint)
variable {p pieces depth:A→ℕ}{b α θ:A→ℝ}{g τ:ℝ}

private theorem split (x:A→ℝ)(φ:A→ℝ) (pos:∀a,0 ≤ x a)(cap:∀a,φ a ≤ τ):
    (∑a:A,x a*φ a) ≤ (∑a:A,x a)*τ:=by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun a _=>mul_le_mul_of_nonneg_left (cap a) (pos a)

theorem regular {G:Gauge}(j m:ℕ)(wallet:∀a,0 < Poly.toll (w a) s)
    (salary:∀a,0 ≤ b a)(width:∀a,0 < θ a)(decay:∀a,Real.exp (-(θ a))^m ≤ τ):
    rent (G:=G) w c ℓ B (p:=p) (pieces:=pieces) (depth:=depth) (b:=b) (α:=α) (θ:=θ) s j m ≤
      rent (G:=G) w c ℓ B (p:=p) (pieces:=pieces) (depth:=depth) (b:=b) (α:=α) (θ:=θ) s j 0*τ:=by
  let base (a:A):=|c a| * WilsonEmittedTransitionJet.fee j (ℓ a) ((Poly.toll (w a) s)⁻¹ *
    Footprint.payment 1 (B.B+2) (j*(p a+depth a+1)) (θ a)
      (fee G j (p a+depth a+1)) (b a) (α a) (Invoice.tax (p a+depth a+1) (pieces a)))
  have bp (a:A):0 ≤ base a:=by
    have pay:=payment (a:=α a) (u:=Invoice.tax (p a+depth a+1) (pieces a)) (width a)
      (fee_pos G j (p a+depth a+1)).le (salary a) 1 (B.B+2) (j*(p a+depth a+1))
    have toll:=wallet a
    unfold base WilsonEmittedTransitionJet.fee Comparison.Density.Render.couple
    positivity
  have z:=split base (fun a=>Real.exp (-(θ a))^m) bp decay
  unfold WilsonEmittedFiledCatalogue.rent WilsonEmittedLocatedCensus.receipt
  simp only [pow_zero,mul_one]
  convert z using 1
  apply Finset.sum_congr rfl
  intro a _
  unfold base WilsonEmittedTransitionJet.fee
  ring

theorem unmasked (m:ℕ)(wallet:∀a,0 < Poly.toll (w a) s)(salary:∀a,0 ≤ b a)
    (width:∀a,0 < θ a)(hg:0<g)(decay:∀a,Real.exp (-(θ a))^m ≤ τ):
    WilsonEmittedLongInvoice.gross w c ν B s m g p pieces depth b θ ≤
      WilsonEmittedLongInvoice.gross w c ν B s 0 g p pieces depth b θ*τ:=by
  let base (a:A):=‖WilsonEmittedLongInvoice.scalar c ν g a‖ * (ceiling g (p a) (depth a)*
    ((Poly.toll (w a) s)⁻¹*Footprint.payment 1 (B.B+2) 0 (θ a) 1 (b a) (B.supportExponent+2)
      (Invoice.tax (p a+depth a+1) (pieces a))))
  have bp (a:A):0 ≤ base a:=by
    have pay:=payment (a:=B.supportExponent+2) (u:=Invoice.tax (p a+depth a+1) (pieces a))
      (width a) zero_le_one (salary a) 1 (B.B+2) 0
    have toll:=wallet a
    unfold base ceiling
    positivity
  have z:=split base (fun a=>Real.exp (-(θ a))^m) bp decay
  unfold WilsonEmittedLongInvoice.gross stock
  simp only [pow_zero,mul_one]
  convert z using 1
  apply Finset.sum_congr rfl
  intro a _
  unfold base
  ring

end YM.Integration.WilsonOriginalPrintedLength
end
