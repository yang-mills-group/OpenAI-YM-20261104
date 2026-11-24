import YM.Integration.WilsonPhysicalExteriorFieldGram
import YM.Integration.WilsonPhysicalExteriorFeePolynomial
import YM.Integration.MSCutoffGerms

/-! The real univariate polynomial on a coherent shift of the three
registered clocks. A lower physical grade can have moderate measured
size only if this original polynomial vanishes identically. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorGradeCoefficient
open Filter MS MS.Land MS.Menus MS.Rake
open WilsonPhysicalExteriorFieldGram WilsonPhysicalExteriorFeePolynomial
open WilsonPhysicalExteriorRunningRows MSCutoffGerms
open scoped Classical
variable {G:Gauge}{B:MS.Local.Physical.Deck G}

def line (s:ℝ) : MvPolynomial (Fin 3) ℝ→+*Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X+Polynomial.C s,Polynomial.X,
    Polynomial.X+Polynomial.C s]

private theorem at_line (s y:ℝ) :
    (Polynomial.evalRingHom y).comp (line s) = MvPolynomial.eval ![y+s,y,y+s] := by
  apply MvPolynomial.ringHom_ext
  · intro r;simp [line]
  · intro i;fin_cases i <;> simp [line]

def receipt (Q:Prescription B) (s:ℝ) (p:Label B) (a:Glyph B p.h) (k:ℕ) : Polynomial ℝ :=
  line s (PowerSeries.coeff k (stored Q p.h (Land.read p.item) a))

theorem coefficient (Q:Prescription B) (s y:ℝ) (p:Label B) (a:Glyph B p.h) (k:ℕ) :
    PowerSeries.coeff k (coordinates Q p.h (y+s) y (y+s) (Land.read p.item) a)=
      (((receipt Q s p a k).eval y:ℝ):ℂ) := by
  have eq:=DFunLike.congr_fun (at_line s y) (PowerSeries.coeff k (stored Q p.h (Land.read p.item) a))
  exact (WilsonPhysicalExteriorFeePolynomial.polynomial Q p.h k (Land.read p.item) a ![y+s,y,y+s]).trans
    (congrArg (fun r:ℝ=>(r:ℂ)) eq.symm)

private theorem engineering (d n:ℕ) (t:ℝ) :
    ((Real.exp (-t):ℂ)⁻¹)^d*(Real.exp (-t):ℂ)^n=(Real.exp (((d:ℝ)-n)*t):ℂ) := by
  rw [←Complex.ofReal_inv,←Complex.ofReal_pow,←Complex.ofReal_pow,←Complex.ofReal_mul]
  apply congrArg (fun u:ℝ=>(u:ℂ))
  rw [←Real.exp_neg,neg_neg,←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
  congr 1;ring

theorem charged (Q:Prescription B) (s y t:ℝ) (p:Label B) (a:Glyph B p.h) (k:ℕ) :
    PowerSeries.coeff k (pay Q y (y+s) (Real.exp (-t)) p a)=
      ((Real.exp (((p.h:ℝ)-a.size)*t)*(receipt Q s p a k).eval y:ℝ):ℂ) := by
  rw [pay,PowerSeries.coeff_C_mul,engineering,coefficient,Complex.ofReal_mul]

theorem regular {I:Type} {l:Filter I} {t:I→ℝ} (ht:Tendsto t l atTop) (Q:Prescription B)
    (s μ:ℝ) (p:Label B) (a:Glyph B p.h) (k:ℕ) (h:a.size=p.h) :
    Moderate l t (fun i=>PowerSeries.coeff k (pay Q (μ-t i) (μ+s-t i) (Real.exp (-t i)) p a)) := by
  have val (i:I): PowerSeries.coeff k (pay Q (μ-t i) (μ+s-t i) (Real.exp (-(t i))) p a)=
      (((receipt Q s p a k).eval (μ-t i):ℝ):ℂ) := by
    rw [show μ+s-t i=(μ-t i)+s by ring,charged,h]
    simp
  simp_rw [val]
  exact MSCutoffGerms.polynomial ht μ (receipt Q s p a k)

theorem excluded {I:Type} {l:Filter I} [NeBot l] {t:I→ℝ} (ht:Tendsto t l atTop)
    (Q:Prescription B) (s μ:ℝ) (p:Label B) (a:Glyph B p.h) (k:ℕ) (h:a.size<p.h)
    (hM:Moderate l t (fun i=>PowerSeries.coeff k
      (pay Q (μ-t i) (μ+s-t i) (Real.exp (-t i)) p a))) :
    ∀ y:ℝ,PowerSeries.coeff k (coordinates Q p.h (y+s) y (y+s) (Land.read p.item) a)=0 := by
  have val (i:I): PowerSeries.coeff k (pay Q (μ-t i) (μ+s-t i) (Real.exp (-(t i))) p a)=
      ((Real.exp (((p.h:ℝ)-a.size)*t i)*(receipt Q s p a k).eval (μ-t i):ℝ):ℂ) := by
    rw [show μ+s-t i=(μ-t i)+s by ring,charged]
  simp_rw [val] at hM
  have zero:=MSCutoffGerms.no_lower ht μ ((p.h:ℝ)-a.size)
    (sub_pos.mpr (by exact_mod_cast h)) (receipt Q s p a k) hM
  intro y;rw [coefficient,zero];simp

end YM.Integration.WilsonPhysicalExteriorGradeCoefficient
end
