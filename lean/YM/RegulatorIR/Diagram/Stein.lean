import YM.RegulatorIR.Diagram.Weyl
import YM.PertExtension.GaussianIBP

/-!
Stein identity for arbitrary polynomials translated by ambient fields and
using one *actual* finite-dimensional Gaussian. Allows a singular matrix on
field legs via a slice, with the ambient covariance the pushforward (never
inverted on the ambient fields).
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram.Gaussian
open Function MvPolynomial Finset MeasureTheory PertExtension Series GaussianScore
open scoped Topology BigOperators Classical PowerSeries
variable {I E : Type}[NormedAddCommGroup E][NormedSpace ℝ E]
   (A:Law E) (d:I→Module.Dual ℝ E)

def probe (b : I→ℝ)(u:Jet I)(x:E):ℝ:=eval (b+fun i=> d i x) u



variable (b:I→ℝ)
lemma probe_add (u v:Jet I) : probe d b (u+v)=probe d b u+probe d b v:=by ext;simp [probe]
lemma probe_mul (u v:Jet I) : probe d b (u*v)=probe d b u*probe d b v:=by ext;simp [probe]
lemma probe_X (i:I)(x:E): probe d b (X i) x=b i+d i x:=by simp [probe]
lemma probe_C (r:ℝ) : probe d b (C r)=fun _=>r:=by ext; simp [probe]

variable [FiniteDimensional ℝ E]
def bond (i j:I) := A.wick (d i) (d j)
lemma bond_cross i j: bond A d i j=bond A d j i:=by
 unfold bond Law.wick
 let X:= A.inverse (d i)
 let Y:= A.inverse (d j)
 calc
   _ = A.P Y X := by rw [show A.P Y=d j from A.applies _]
   _ = A.P X Y:= A.turns _ _
   _ = _:= by rw [show A.P X=d i from A.applies _]
lemma proper (u:Jet I): Radial.zone.Invoice (probe d b u) ∧ Continuous (probe d b u) := by
 induction u using MvPolynomial.induction_on with
 | C r=> rw [probe_C]; exact ⟨Zone.Invoice.const _,continuous_const⟩
 | add x y h hx=>rw [probe_add]; exact ⟨h.1.add hx.1,h.2.add hx.2⟩
 | mul_X x i h=>
    rw [probe_mul]; rw [show probe d b (X i)=(fun _=>b i)+(fun x=>d i x) from funext (fun x=>probe_X d b i x)]
    exact ⟨h.1.mul ((Zone.Invoice.const (b i)).add (Law.linearInvoice (d i))), h.2.mul (continuous_const.add ((d i).continuous_of_finiteDimensional))⟩

variable [MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.HasTemperateGrowth]

def averaged (A:Law E) (d:I→Module.Dual ℝ E)(μ:Measure E)(b:I→ℝ)(u:Jet I) := A.average μ (probe d b u)
lemma accept (u: Jet I):Integrable (probe d b u * A.kern) μ:= A.integrable_entry _ (proper d b u).1 (proper d b u).2
lemma average_add (u v:Jet I): averaged A d μ b (u+v)=averaged A d μ b u+averaged A d μ b v:=by unfold averaged Law.average; rw [probe_add, add_mul]; simp_rw [Pi.add_apply]; rw [integral_add (accept A d b μ u) (accept A d b μ v),add_div]
lemma average_const [NeZero μ] (r:ℝ) : averaged A d μ b (C r)=r:= by
 have he:= A.empty μ
 calc
  _ = A.average μ (fun _=>r):= congr_arg _ (probe_C ..)
  _ = r * A.average μ 1 := by unfold Law.average; rw [one_mul]; simp only [Pi.mul_apply]; rw [integral_const_mul];ring
  _ = _:= by rw [he,mul_one]

variable [Fintype I]
def increase (δ:E)(u:Jet I): Jet I:= ∑ i,C (d i δ)*MvPolynomial.pderiv i u
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma along (a δ:E)(u:Jet I)(t:ℝ) : HasDerivAt (fun r:ℝ=>probe d b u (a+r • δ)) (probe d b (increase d δ u) (a+t • δ)) t := by
 induction u using MvPolynomial.induction_on with
 | C r=> simp only [increase,pderiv_C,mul_zero,sum_const_zero,probe_C]; rw [show probe d b 0 _=0 from by simp [probe]]; exact hasDerivAt_const ..
 | add f g h k =>
    simp_rw [show increase d δ (f+g)=increase d δ f+increase d δ g from by simp_rw [increase,map_add,mul_add,sum_add_distrib],probe_add]
    exact h.add k
 | mul_X f i h=>
    have he : HasDerivAt (fun r:ℝ=>probe d b (X i) (a+r • δ)) (d i δ) t:=by simp_rw [probe_X,map_add,map_smul,smul_eq_mul]; simpa only [one_mul] using! (((hasDerivAt_id' t).mul_const (d i δ)).const_add _).const_add _
    have hk: increase d δ (f*X i)= increase d δ f * X i + C (d i δ)*f := by
       unfold increase; simp only [pderiv_mul,mul_add,sum_add_distrib]; congr 1
       · rw [sum_mul]; exact sum_congr rfl fun i _=> by ring
       classical
       simp only [pderiv_X,Pi.single_apply]; simp [mul_ite]
    simp_rw [probe_mul]
    rw [hk,probe_add]; have hs:=h.mul he;
    convert hs using 1 <;> first | rfl | (simp [probe]; ring)

omit A [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma increase_v (δ:E)(u:Jet I)(x:E): probe d b (increase d δ u) x = ∑ i, d i δ * probe d b (MvPolynomial.pderiv i u) x:= by simp [increase,probe]
include A
variable [μ.IsAddRightInvariant]

lemma recipe (u:Jet I) (i:I):
 averaged A d μ b (u * X i) = b i * averaged A d μ b u + ∑ j,bond A d i j * averaged A d μ b (MvPolynomial.pderiv j u):=by
 let T:=probe d b u; let v:=A.inverse (d i); let L:= increase d v u
 let W:=probe d b L
 have hL: Integrable (W * A.kern) μ := accept A d b μ L
 have ht:=A.translation_lemma v (A:=T) (L:=W) (proper d b u).1 (proper d b u).2 (proper d b L).1 (proper d b L).2 (fun a t=>along ..) μ
 -- Stein with linear leg
 let q := (fun x=> A.P v x)
 have hv': A.P v=d i:= A.applies _
 have hg: Integrable ((T*q) * A.kern) μ:= A.integrable_entry _ ((proper d b u).1.mul (Law.linearInvoice (A.P v))) ((proper d b u).2.mul ((A.P v).continuous_of_finiteDimensional))
 have HH : (∫ x, W x * A.kern x ∂μ)= ∫ x,T x*q x * A.kern x ∂μ := sub_eq_zero.mp (by
    change (∫ x, (W*A.kern) x ∂μ) - (∫ x,(T*q*A.kern) x ∂μ)=0; rw [← integral_sub hL hg]; rw [sub_mul] at ht; exact ht)
 let Cj j := fun x:E=> probe d b (pderiv j u) x*A.kern x
 have hu:(∫ x,(probe d b (u*X i) * A.kern) x ∂μ)=b i*(∫ x,T x*A.kern x ∂μ)+(∑ j,bond A d i j * ∫ x,Cj j x ∂μ):=by
   calc
    _ = ∫ x,b i*(T x *A.kern x)+T x*q x*A.kern x ∂μ:=by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x=>?_))
      rw [probe_mul,Pi.mul_apply,Pi.mul_apply,probe_X]; dsimp only; rw [show q x=d i x from by unfold q;rw [hv']]; unfold T; ring
    _ = b i*(∫ x,T x*A.kern x ∂μ)+∫ x,W x*A.kern x ∂μ := by rw [integral_add _ (show Integrable (fun x=>T x*q x*A.kern x) μ from hg),integral_const_mul, HH]; exact (accept A d b μ u).const_mul (b i)
    _ = _:= by
       apply congr_arg
       have he x : W x * A.kern x =∑ j,bond A d i j*Cj j x:=by unfold W L; rw [increase_v,sum_mul]; exact sum_congr rfl fun j _ => by unfold bond Cj v Law.wick; rw [mul_assoc]
       simp_rw [he]; rw [integral_finsetSum]; simp_rw [integral_const_mul]; exact fun _ _=> (accept ..).const_mul _
 unfold averaged Law.average
 rw [hu,add_div,mul_div_assoc, Finset.sum_div]
 exact congr_arg₂ (·+·) rfl (Finset.sum_congr rfl fun _ _=> mul_div_assoc ..)
end YM.RegulatorIR.Diagram.Gaussian
