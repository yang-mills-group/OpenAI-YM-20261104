import YM.OPE.Compatible.Silva.Part
/-!
# Berk averages, normalized local laws
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Flock
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset
variable {E F I:Type}
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
variable (μ:Measure E)[μ.IsAddHaarMeasure] (L: Law E)
lemma bask (v:E)(x y:E→ℝ)(h:Bond x)(hp:Bond y)(hx:∀ a t, HasDerivAt (fun k:ℝ=> x (a+k • v)) (y (a+t•v)) t): L.average μ ((L.P v) * x)=L.average μ y:=by
     have hb := L.translation_lemma v h.cost h.smooth.continuous hp.cost hp.smooth.continuous hx μ
     rw [sub_mul] at hb; simp only [Pi.sub_apply] at hb; rw [integral_sub (lumpZ _ L _ hp) (lumpZ _ L _ (h.mul (Bond.glyph (L.P v))))] at hb; unfold Law.average; rw [mul_comm ⇑(L.P v)]; exact congr_arg (fun x:ℝ=> x/_) (sub_eq_zero.mp hb).symm
lemma colorful (p:E→ℝ)(h:Bond p)(k:∀ x,p (-x)= -p x):L.average μ p=0:=by
     let P:E≃ₗ[ℝ] E:= LinearEquiv.neg ℝ; have hh: L.average μ p=L.average μ (p ∘ P):=meanFit μ μ L L P.toLinearMap (dual_wick P L L (by intro i; change _=L.P (-i) (-i);simp)) p h; rw [show p ∘ P = (-1:ℝ) • p from funext fun i=> by change p (-i)=(-1:ℝ)*p i; rw [k];ring, scooted] at hh; linarith only [hh]
lemma summer (a b: Dual' E):L.average μ (⇑a*⇑b)=L.wick a b:=by
    rw [← singleConst μ L (L.wick a b)]; -- accidentally rewrites LHS if repeats?
    let v:=L.inverse a; refine Eq.trans (congr_arg (L.average μ) (show ⇑a*⇑b=⇑(L.P v)*b from (L.applies a).symm ▸ rfl)) ?_; apply bask μ L v b (fun _=> L.wick a b) (Bond.glyph b) (Bond.keep _); intro x t; show HasDerivAt _ (b v) _; simp only [map_add,map_smul,smul_eq_mul]; simpa using! HasDerivAt.const_add (b x) ((hasDerivAt_id' t).mul_const (b v))
lemma squareQ (a b c d:Dual' E):L.average μ (⇑a*⇑b*⇑c*⇑d) = L.wick a b* L.wick c d+ L.wick a c*L.wick b d+L.wick a d * L.wick b c:=by
    let v:=L.inverse a; let A:= ⇑a; let B:=⇑b; let C:=⇑c; let D:=⇑d; let P:=B*C*D; let X:= c v • (B*D)+d v • (B*C); let T:=b v • (C*D)+ X
    have hp:Bond T:= ((Bond.scale _ ((Bond.glyph c).mul (Bond.glyph d)))).add ((Bond.scale _ ((Bond.glyph b).mul (Bond.glyph d))).add (Bond.scale _ ((Bond.glyph b).mul (Bond.glyph c))))
    have hh(z:Dual' E)(x:E)(t:ℝ): HasDerivAt (fun i:ℝ=>z (x+i • v)) (z v) t:=by simp only [map_add,map_smul,smul_eq_mul]; simpa using! HasDerivAt.const_add (z x) ((hasDerivAt_id' t).mul_const (z v))
    have he(x t): HasDerivAt (fun i:ℝ=>P (x+i • v)) (T (x+t • v)) t:=by
         let u:=x+t • v; convert! (((hh b x t).mul (hh c x t)).mul (hh d x t)) using 1; simp only [T,X,Pi.add_apply,Pi.smul_apply,Pi.mul_apply,smul_eq_mul]; change b v*(c u*d u)+(c v*(b u*d u)+d v*(b u*c u))=(b v*c u+b u*c v)*d u+b u*c u*d v;ring
    change L.average μ (A*B*C*D) =_ ; rw [show A*B*C*D=⇑(L.P v)*P from ?_,bask μ L v P T _ hp he]; unfold T X; have hx:Bond (C*D):= (Bond.glyph c).mul (Bond.glyph d); have hv:Bond (B*C):= (Bond.glyph b).mul (Bond.glyph c); have hy:Bond (B*D):=(Bond.glyph b).mul (Bond.glyph d); rw [sun μ L (Bond.scale _ hx) ((Bond.scale _ hy).add (Bond.scale _ hv)),sun μ L (Bond.scale _ hy) (Bond.scale _ hv), scooted,scooted,scooted,summer μ L c d,summer μ L b c,summer μ L b d]; rw [add_assoc]; rfl
    · exact (((Bond.glyph b).mul (Bond.glyph c)).mul (Bond.glyph d) : Bond P)
    unfold v P A; rw [L.applies]; ring
lemma science (s:Finset I)(p:I→E→ℝ)(h:∀ i∈s, Bond (p i)): L.average μ (∑ i∈s,p i)=∑ i∈s,L.average μ (p i):=by
     induction s using Finset.induction_on with
     | empty=>exact by simpa only [sum_empty] using! singleConst μ L 0
     | insert i s hi ih=> simp only [sum_insert hi]; rw [sun μ L (h i (mem_insert_self ..)) (show Bond (∑ i∈s,p i) by rw [show (∑ i∈s,p i)=fun x=>∑ i∈s,p i x from funext fun x=>sum_apply x ..]; exact Bond.sum p s (fun j he=>h j (mem_insert_of_mem he)) ),ih (fun i he=> h i (mem_insert_of_mem he))]
include μ
lemma wix_sym (a b:Dual' E): L.wick a b=L.wick b a:=by rw [← summer μ L,← summer μ L,mul_comm]
end YM.OPE.Libra.Flock
