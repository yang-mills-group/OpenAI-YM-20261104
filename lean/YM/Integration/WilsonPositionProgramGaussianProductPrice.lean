import YM.Integration.WilsonPositionProgramRecastInputInvoice
import YM.Integration.WilsonMovingGaussianGeometry
import YM.Integration.WilsonMarkedInheritedGaussianMoment

/-! Actual finite Gaussian moments of an original product and a single substituted factor. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramGaussianProductPrice
open Finset MeasureTheory RG Marker Multi Comparison.RG02 Next.SectorChange
open Next.Rank Next.SectorChange.Gaussian Comparison.RG02.Cumulants WilsonMarkedInheritedGaussianMoment
open scoped BigOperators Classical
variable {I:Type}[Fintype I][DecidableEq I]

theorem measured (Q:Matrix I I ℝ)(hq:Q.PosDef)(hQ:Q.IsSymm)(σ:ℝ)(diag:∀i,Q i i≤σ)
    (F:Normal.poly I)(k:ℕ){b:ℝ}(hb:0≤b)
    (paid:∀z:I→ℝ,‖Cloud.paint z F‖≤b*(1+‖z‖)^k):
    ‖Cloud.wick Q hQ (Cloud.shift (0:I→ℝ)) F‖≤ b*charge I σ k := by
  obtain ⟨finite,eval⟩:=Cloud.paid Q hQ hq.posSemidef (0:I→ℝ) F
  simp only [zero_add] at finite eval
  rw [←eval,←WilsonMovingGaussianGeometry.law]
  rw [←WilsonMovingGaussianGeometry.law] at finite
  obtain ⟨funP,area⟩:=WilsonMarkedInheritedGaussianMoment.complete hq σ diag k
  calc
    _≤∫z,‖Cloud.paint z F‖ ∂Further.GaussianScalar.fieldLaw Q :=norm_integral_le_integral_norm _
    _≤∫z,b*(1+‖z‖)^k ∂Further.GaussianScalar.fieldLaw Q :=integral_mono finite.norm (funP.const_mul b) paid
    _≤_:=by rw [integral_const_mul];exact mul_le_mul_of_nonneg_left area hb

variable {T:Type}

theorem mass (u:Finset T)(P:T→ℂ){B:ℝ}(hp:∀i,‖P i‖≤B):
    ‖∏i∈u,P i‖ ≤B^u.card:=by
  rw [norm_prod]
  exact (prod_le_prod (fun i _=>norm_nonneg (P i)) (fun i _=>hp i)).trans_eq (by simp)

theorem change (u:Finset T)(P Q:T→ℂ){B δ:ℝ}(hb:1≤B)(hd:0≤δ)
    (hp:∀i,‖P i‖≤B)(hq:∀i,‖Q i‖≤B)(fee:∀i,‖P i-Q i‖≤δ):
    ‖(∏i∈u,P i)-(∏i∈u,Q i)‖ ≤ (u.card:ℝ)*δ*B^u.card:=by
  induction u using Finset.induction_on with
  | empty=>simp
  | @insert i u off ih=>
    rw [prod_insert off,prod_insert off,card_insert_of_notMem off]
    have moved: P i*(∏j∈u,P j)-Q i*(∏j∈u,Q j)=
        P i*((∏j∈u,P j)-(∏j∈u,Q j))+(P i-Q i)*(∏j∈u,Q j):=by ring
    rw [moved]
    calc
      _≤‖P i‖*‖(∏j∈u,P j)-(∏j∈u,Q j)‖+‖P i-Q i‖*‖∏j∈u,Q j‖:=by
        simpa only [norm_mul] using norm_add_le (P i*((∏j∈u,P j)-(∏j∈u,Q j))) ((P i-Q i)*(∏j∈u,Q j))
      _≤B*((u.card:ℝ)*δ*B^u.card)+δ*B^u.card:=by
        exact add_le_add (mul_le_mul (hp i) ih (norm_nonneg _) (zero_le_one.trans hb))
          (mul_le_mul (fee i) (mass u Q hq) (norm_nonneg _) hd)
      _≤_:=by
        have grown:δ*B^u.card≤δ*B^u.card*B:=le_mul_of_one_le_right (by positivity) hb
        push_cast;rw [pow_succ]
        linarith

end YM.Integration.WilsonPositionProgramGaussianProductPrice
end
