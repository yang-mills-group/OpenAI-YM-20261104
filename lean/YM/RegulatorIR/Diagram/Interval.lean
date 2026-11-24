import YM.RegulatorIR.Diagram.Packed
import YM.RegulatorIR.Diagram.Expo

/-!
Time polynomials and series with time-polynomial coefficients. Differentiate
one variable holding every other variable fixed. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram.Interval
open Function Budget Budget.Layer Formal PowerSeries
open scoped Topology ENNReal NNReal BigOperators Classical Polynomial PowerSeries
variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℝ R] [Algebra ℝ S]

private def outPoly (D:Derivation ℝ R R)(p:R[X]) : R[X] := ∑ i∈p.support, Polynomial.monomial i (D (p.coeff i))
private lemma outPoly_v (D:Derivation ℝ R R)(p:R[X])(i): (outPoly D p).coeff i=D (p.coeff i):= by
 by_cases h:i∈p.support
 · simp [outPoly,Polynomial.coeff_monomial,h]
 simp [outPoly,Polynomial.coeff_monomial,h, Polynomial.notMem_support_iff.mp h]

def remaining (D:Derivation ℝ R R):Derivation ℝ R[X] R[X] where
 toFun:=outPoly D
 map_add' P Q:= by ext i; simp only [outPoly_v,Polynomial.coeff_add, map_add]
 map_smul' r P:= by ext i; change (outPoly D (r • P)).coeff i=(r • outPoly D P).coeff i; rw [outPoly_v,Polynomial.coeff_smul,Polynomial.coeff_smul,D.map_smul,outPoly_v]
 map_one_eq_zero':=by ext i;change (outPoly D 1).coeff i=_; rw [outPoly_v]; simp [Polynomial.coeff_one,apply_ite D]
 leibniz' a b:= by
   ext i;change (outPoly D (a*b)).coeff i=(a*outPoly D b+b*outPoly D a).coeff i
   rw [outPoly_v,Polynomial.coeff_mul, map_sum,Polynomial.coeff_add]; simp_rw [Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib, Polynomial.coeff_mul, outPoly_v]
   congr 1
   exact Finset.sum_bij (fun a ha=> (a.2,a.1)) (fun a h=> Finset.mem_antidiagonal.mpr ((add_comm ..).trans (Finset.mem_antidiagonal.mp h))) (fun a _ b _ h=> Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1) (fun a h=> ⟨(a.2,a.1),Finset.mem_antidiagonal.mpr ((add_comm ..).trans (Finset.mem_antidiagonal.mp h)),rfl⟩) (fun _ _=> rfl)
lemma remaining_v (D:Derivation ℝ R R)(p:R[X])(i): (remaining D p).coeff i=D (p.coeff i):=outPoly_v ..

def clock (R:Type) [CommRing R][Algebra ℝ R]:Derivation ℝ R[X] R[X] where
 toFun:= Polynomial.derivative
 map_add':=fun f g=>map_add Polynomial.derivative _ _
 map_smul' a p:= by
    ext i; simp only [Polynomial.coeff_derivative,Polynomial.coeff_smul,RingHom.id_apply]; rw [smul_mul_assoc]
 map_one_eq_zero':= Polynomial.derivative_one
 leibniz' a b:= by change Polynomial.derivative (a*b) = a*Polynomial.derivative b+b*Polynomial.derivative a; rw [Polynomial.derivative_mul]; ring
lemma clock_v (p:R[X])(i): (clock R p).coeff i= p.coeff (i+1)*(i+1):=by change (Polynomial.derivative _).coeff _= _; rw [Polynomial.coeff_derivative]

section lap
variable {I:Type}[Fintype I]
abbrev CurveT (I:Type):= Polynomial (Jet I)
abbrev EPS (I:Type):= PowerSeries (CurveT I)

omit [Fintype I] in
lemma band_const (K:ℝ) (f:EPS I)(e t:ℕ): (coeff e (algebraMap ℝ (EPS I) K * f)).coeff t=MvPolynomial.C K * (coeff e f).coeff t:=by
 rw [← Algebra.smul_def, coeff_smul, Polynomial.coeff_smul,Algebra.smul_def]; rfl

def blade (i:I): Derivation ℝ (CurveT I) (CurveT I):=remaining (MvPolynomial.pderiv i)
def vane (i:I): Derivation ℝ (EPS I) (EPS I):=farther (blade i)

def sweepN (K:Layer I I)(p:CurveT I): CurveT I:= ∑ i:I,∑ j:I,K i j • blade i (blade j p)
def sweepF (K:Layer I I)(W:EPS I): EPS I:= ∑ i:I,∑ j:I,K i j • vane i (vane j W)
def meetF (K:Layer I I)(V W:EPS I): EPS I:= ∑ i:I,∑ j:I, (K i j • (vane i V * vane j W))

omit [Fintype I] in
lemma higher_v (i:I)(P:EPS I)(e) : coeff e (vane i P)=blade i (coeff e P):= farther_v ..
omit [Fintype I] in
lemma vane_v (i:I)(P:EPS I)(e t) : (coeff e (vane i P)).coeff t= MvPolynomial.pderiv i ((coeff e P).coeff t):= by rw [higher_v]; exact remaining_v ..
lemma sweepF_v (K:Layer I I)(P:EPS I)(e): coeff e (sweepF K P)= sweepN K (coeff e P):=by simp_rw [sweepF,map_sum,coeff_smul,higher_v]; rfl
lemma sweepN_v (K:Layer I I)(P:CurveT I)(t): (sweepN K P).coeff t=sweep K (P.coeff t):=by simp_rw [sweepN,Polynomial.finsetSum_coeff,Polynomial.coeff_smul, blade,remaining_v]; simp_rw [sweep,Algebra.smul_def]; rfl
lemma meetF_v (K : Layer I I)(P Q:EPS I)(e t):
    (coeff e (meetF K P Q)).coeff t = ∑ q∈ Finset.antidiagonal t,∑ p∈ Finset.antidiagonal e,
       meet K ((coeff p.1 P).coeff q.1) ((coeff p.2 Q).coeff q.2):= by
 unfold meetF meet; simp_rw [map_sum,Polynomial.finsetSum_coeff, coeff_smul,Polynomial.coeff_smul, coeff_mul, Polynomial.finsetSum_coeff,Polynomial.coeff_mul,vane_v]
 simp_rw [Finset.smul_sum,Algebra.smul_def, show ∀ r:ℝ, algebraMap ℝ (Jet I) r=MvPolynomial.C r from fun r=>rfl,mul_assoc]
 simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.antidiagonal e), Finset.sum_comm (s:=Finset.univ) (t:=Finset.antidiagonal t)]
 rw [Finset.sum_comm]
end lap
end YM.RegulatorIR.Diagram.Interval
