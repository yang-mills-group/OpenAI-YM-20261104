import YM.Integration.WilsonOriginalSingleGaussianTable

/-! Original finite Gaussian integration of the complete ordinary source roster. The
square-zero coefficient in each row may itself be the product of earlier source faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedGaussianTable
open Function Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonVacuumPreResetFiniteRegister
open OriginalRadialSeries (observed)
open scoped Classical BigOperators
variable {V:Type}[Fintype V][DecidableEq V](J:Census V)(r:ℕ)
variable {S A:Type}[Fintype A]

def term (B:S→ℝ)(a:Poly J)(T:Ink S):Grade J r :=
  Join.injectLeft J (indices r) a * register J r (observed B T)

def stock (B:S→ℝ)(a:A→Poly J)(T:A→Ink S):Grade J r :=
  ∑e,term J r B (a e) (T e)

theorem term_value (B:S→ℝ)(a:Poly J)(T:Ink S)(t:J.Mode)(u:Index r):
    (term J r B a T).part (Join.pair t u)=
      (a.part t*(u.val.card.factorial:ℂ))*(MvPolynomial.eval B (coeff u.val.card T):ℝ):=by
  unfold term
  rw [←WilsonOriginalSingleMarkedRegister.clean J r (observed B T),bottom,AlgHom.comp_apply,Join.separate]
  change a.part t*(register J r (observed B T)).part (Join.pair J.quiet u)=_
  rw [WilsonVacuumPreResetFiniteRegister.read,if_pos rfl]
  change a.part t*((u.val.card.factorial:ℂ)*(MvPolynomial.eval B (coeff u.val.card T):ℝ))=_
  rw [mul_assoc]

theorem value (B:S→ℝ)(a:A→Poly J)(T:A→Ink S)(t:J.Mode)(u:Index r):
    (stock J r B a T).part (Join.pair t u)=
      ∑e,((a e).part t*(u.val.card.factorial:ℂ))*(MvPolynomial.eval B (coeff u.val.card (T e)):ℝ):=by
  simp only [stock,Poly.part_sum,term_value]

theorem integrated {I Y:Type}[Fintype I][DecidableEq I][Fintype Y] (B:Y→ℝ)
    (q:Matrix I I ℝ)(h:q.IsSymm)(a:A→Poly J)(T:A→Ink (I⊕Y))(f:Hot (Board J r)→Normal.poly I)
    (law:∀z,Poly.pass (lit (Board J r) (fun s=>Cloud.paint z (f s)))=stock J r (Sum.elim z B) a T):
    Cloud.prescription q h 0 f=stock J r B a (fun e=>Wick Y q (T e)):=by
  apply Join.both_parts
  intro t u
  change Cloud.wick q h 0 (Cloud.integrand f (Join.pair t u))=_
  rw [value]
  apply WilsonOriginalSingleGaussianTable.integrated B q h u.val.card T
  intro z
  rw [Cloud.before_log,law,value]

end YM.Integration.WilsonOriginalMixedGaussianTable
