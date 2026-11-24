import YM.Integration.WilsonMSDictionaryFarRead

/-! Multiplication of evaluated finite Taylor polynomials adds precisely
the terms above the retained total degree on the finite rectangle. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkSeriesProduct
open Filter Function Finset PowerSeries WilsonMSDictionaryFarRead
open scoped Classical BigOperators

def rectangle (q:ℕ):Finset (ℕ×ℕ):=Finset.product (range (q+1)) (range (q+1))
def high (q:ℕ):Finset (ℕ×ℕ):=(rectangle q).filter fun p=> ¬p.1+p.2∈range (q+1)
def term (t:ℝ)(a b:PowerSeries ℂ)(p:ℕ×ℕ):ℂ:=(t:ℂ)^(p.1+p.2)*coeff p.1 a*coeff p.2 b

theorem late {q:ℕ}{p:ℕ×ℕ}(hp:p∈high q):q+1≤p.1+p.2:=by
  have := (Finset.mem_filter.mp hp).2
  simpa using this

theorem square (q:ℕ)(t:ℝ)(a b:PowerSeries ℂ):
    cutoff q t a*cutoff q t b-cutoff q t (a*b)=∑p∈high q,term t a b p:=by
  let r:=rectangle q
  have fibre(k:ℕ)(hk:k∈range (q+1)):r.filter (fun p=>p.1+p.2=k)=Finset.HasAntidiagonal.antidiagonal k:=by
    ext p
    simp [r,rectangle,Finset.HasAntidiagonal.mem_antidiagonal]
    have hk':=mem_range.mp hk
    omega
  have low:cutoff q t (a*b)=∑p∈r.filter (fun p=>p.1+p.2∈range (q+1)),term t a b p:=by
    rw [← Finset.sum_fiberwise_eq_sum_filter r (range (q+1)) (fun p=>p.1+p.2) (term t a b)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [fibre k hk,coeff_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [term,Finset.HasAntidiagonal.mem_antidiagonal.mp hp];ring
  have full:cutoff q t a*cutoff q t b=∑p∈r,term t a b p:=by
    change _=∑p∈range (q+1) ×ˢ range (q+1),term t a b p
    unfold cutoff
    rw [Finset.sum_product,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [term]
    rw [pow_add];ring
  have split:=Finset.sum_filter_add_sum_filter_not r (fun p=>p.1+p.2∈range (q+1)) (term t a b)
  rw [full,low,←split]
  abel

end YM.Integration.WilsonPublicForkSeriesProduct
