import YM.Integration.WilsonSeparatedOriginalSlabCubicDebit

/-! The first perturbative coefficient of the signed three-observable connected combination. -/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalSlabTaylorCubic
open Finset
open scoped Classical BigOperators
abbrev Row:=Finset (Fin 3)

def ledger {A:Type*}[Ring A](P:Row→A):A:=
  P univ-(P {0,1}*P {2}+P {0,2}*P {1}+P {1,2}*P {0})+
    (P {0}*P {1}*P {2}+P {0}*P {1}*P {2})

def one (c d:Row→ℂ):ℂ:=
  d univ-
    ((d {0,1}*c {2}+c {0,1}*d {2})+
     (d {0,2}*c {1}+c {0,2}*d {1})+
     (d {1,2}*c {0}+c {1,2}*d {0}))+
    2*(d {0}*c {1}*c {2}+c {0}*d {1}*c {2}+c {0}*c {1}*d {2})

theorem crossed (P Q:Polynomial ℂ):
    (P*Q).coeff 1=P.coeff 0*Q.coeff 1+P.coeff 1*Q.coeff 0:=by
  have diag:HasAntidiagonal.antidiagonal (1:ℕ) = {(0,1),(1,0)}:=by decide
  rw [Polynomial.coeff_mul,diag]
  simp

theorem first (P:Row→Polynomial ℂ):
    (ledger P).coeff 1=one (fun J=>(P J).coeff 0) (fun J=>(P J).coeff 1):=by
  simp only [ledger,one,Polynomial.coeff_add,Polynomial.coeff_sub,crossed,Polynomial.mul_coeff_zero]
  ring

theorem measured (P:Row→Polynomial ℂ)(g:ℂ):
    (ledger P).eval g=WilsonSeparatedOriginalMarkedCubic.cubic (fun J=>(P J).eval g):=by
  simp only [ledger,WilsonSeparatedOriginalMarkedCubic.cubic,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul]
  ring

theorem vacuum (P:Row→Polynomial ℂ):
    (ledger P).coeff 0=WilsonSeparatedOriginalMarkedCubic.cubic (fun J=>(P J).coeff 0):=by
  simp only [ledger,WilsonSeparatedOriginalMarkedCubic.cubic,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.mul_coeff_zero]
  ring

end YM.Integration.WilsonSeparatedOriginalSlabTaylorCubic
