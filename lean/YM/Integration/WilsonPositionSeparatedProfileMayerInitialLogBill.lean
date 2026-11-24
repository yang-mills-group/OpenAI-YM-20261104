import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogDegree
import YM.IterationFour.Series.Tail
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-! Summing the independently computed connected thermal tail uses at most one factor for
each physical marker. The polynomial mass is the original finite coefficient bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogBill
open Function Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}

private def pricing (w:V→ℝ) (hw:∀i,0<w i):RingSeminorm (Poly Γ) where
  toFun:=Poly.price w
  map_zero':=by simp [Poly.price]
  add_le':=Poly.addition hw
  neg':=fun p=>by simp [Poly.price]
  mul_le':=Poly.multiplication hw

def entire (w:V→ℝ) (p:Truncated Γ):ℝ:=∑i∈p.support,Poly.price w (p.coeff i)

theorem tail {r:ℕ} {x:Grade Γ r} (lead:UnitLeading x) (w:V→ℝ) (hw:∀i,0<w i)
    (A:ℝ) (wallet:entire w (render (ratio x))≤A):
    subtotal w r 1 (logSeries (Fintype.card V+r) (render (ratio x)))≤
      ∑i∈Finset.range (Fintype.card V),(1+A)^(i+1):=by
  classical
  letI : SeminormedRing (Poly Γ):=(pricing w hw).toSeminormedRing
  letI : NormOneClass (Poly Γ):=⟨Poly.one_price (w:=w)⟩
  let p:=render (ratio x)
  have one:IterationFour.Series.mass (1:Truncated Γ)=1:=
    (IterationFour.Series.prices_monomial (1:Poly Γ) 0).trans norm_one
  have dollar:IterationFour.Series.mass (1-p)≤1+A:=
    (IterationFour.Series.mass_sub (1:Truncated Γ) p).trans (add_le_add one.le wallet)
  have gone (i:ℕ):IterationFour.Series.mass
      (Polynomial.C (algebraMap ℂ (Poly Γ) (-((↑(i+1):ℂ))⁻¹)))≤1:=by
    rw [show Polynomial.C (algebraMap ℂ (Poly Γ) (-((↑(i+1):ℂ))⁻¹))=
      Polynomial.monomial 0 (algebraMap ℂ (Poly Γ) (-((↑(i+1):ℂ))⁻¹)) from rfl,
      IterationFour.Series.prices_monomial]
    change Poly.price w (Poly.bead Γ (-((↑(i+1):ℂ))⁻¹))≤1
    change Poly.price w (Poly.send Γ.quiet (-((↑(i+1):ℂ))⁻¹))≤1
    simp
    rw [←Nat.cast_succ,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i))
  rw [WilsonPositionSeparatedProfileMayerInitialLogDegree.reduced lead]
  let a:=Fintype.card V
  calc
    _≤entire w (logSeries a p):=by
      simp only [subtotal,one_pow,one_mul,entire]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _=>Poly.nonnegative hw _)
    _≤∑i∈Finset.range a,IterationFour.Series.mass
        (Polynomial.C (algebraMap ℂ (Poly Γ) (-((↑(i+1):ℂ))⁻¹))*(1-p)^(i+1)):=
      IterationFour.Series.mass_sum _ _
    _≤_:=by
      apply Finset.sum_le_sum
      intro i _
      have pw:IterationFour.Series.mass ((1-p)^(i+1))≤(1+A)^(i+1):=
        (IterationFour.Series.mass_pow _ _).trans (pow_le_pow_left₀ (IterationFour.Series.mass_nn _) dollar _)
      simpa using (IterationFour.Series.mass_mul _ _).trans
        (mul_le_mul (gone i) pw (IterationFour.Series.mass_nn _) zero_le_one)

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogBill
