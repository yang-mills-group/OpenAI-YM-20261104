import YM.MS.City.Lines
import YM.MS.Menus.B2
import YM.MS.Heat.GridStation
/-!
# Elementary Landau lattice dyad

Use absolute heat length, real values all t even for extension through zero.
 Need composition/closures before flow analysis. Shared with strict dimension calculus.
 Here formulas use finite sum metric.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real
open Complex (I)
open scoped Topology ContDiff
variable {D A :Type}[Fintype D][DecidableEq D] [Fintype A][DecidableEq A]
variable {G:Gauge}
-- polynomial weights heat profile

def X0(r:ℝ): YMflow D:= laplace (low r)
def X1 (r:ℝ): YMflow D:= laplace (fun p=> -2*brush r p*p.sq^2)
lemma brushed (r:ℝ)(i k:Atom D)(p:Momentum D) : (r:ℂ)*L0 r i k p=line r i k p := by
   rcases i with ⟨_|i,_|_⟩ <;> rcases k with ⟨_|k,_|_⟩ <;> simp only [L0,line,mul_zero] <;> first| rfl| (unfold coat brush; simp only [k_scale,scaling,Pi.smul_apply, smul_eq_mul]; push_cast; ring)
lemma lap1 (r:ℝ)(i k:Atom D)(p:Momentum D) : (r:ℂ)*X1 r i k p= laplace (dotLow r) i k p:= by rcases i with ⟨_|i,_|_⟩ <;> rcases k with ⟨_|k,_|_⟩ <;> simp only [X1,laplace,dotLow, brush,delta,coat,scaling,mul_zero] <;> (try split_ifs) <;> push_cast <;> ring
omit [DecidableEq D] in
lemma xH (r:ℝ)(p:Momentum D): HasDerivAt (fun r:ℝ=>low r p) (-2*brush r p*p.sq^2) r:= by
   unfold low coat brush; simp only [scaling, pow_zero, one_mul]; have hu : HasDerivAt (fun r:ℝ=> r^2*p.sq) (2*r*p.sq) r:= by convert! (((hasDerivAt_pow 2 r).mul_const (p.sq))) using 1; simp -- inspect
   convert! ((hu.const_add 1).mul hu.neg.exp) using 1; rw [Pi.neg_apply]; ring
lemma lap_der (r:ℝ)(i k:Atom D)(p: Momentum D): HasDerivAt (fun t=>X0 t i k p) (X1 r i k p) r:= by
   let K: ℝ→ℝ:=fun t=> low t p; have h:= Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r (xH r p)
   rcases i with ⟨_|i,_|_⟩ <;> rcases k with ⟨_|k,_|_⟩ <;> first| exact hasDerivAt_const ..| (unfold X1 X0; simp only [laplace, delta]; first| exact h.neg.div_const _ | (split <;> first| exact h.div_const _ | simpa only [Complex.ofReal_zero,zero_div] using hasDerivAt_const r (0:ℂ)))
lemma L_change (r:ℝ)(i k:Atom D)(p:Momentum D): Plane.Charge.change (stamp id) (L0 r) i k p=X1 r i k p:= by
   by_cases he:r=0; · subst r; rw [show L0 0 =(0:YMflow D) from ?_, show X1 0=(0:YMflow D) from ?_]; simp [Plane.Charge.change]
                      swap; · funext i j p; rcases i with ⟨_|i,_|_⟩ <;> rcases j with ⟨_|j,_|_⟩ <;> simp [L0,brush]
                      funext i j p; rcases i with ⟨_|i,_|_⟩ <;> rcases j with ⟨_|j,_|_⟩ <;> simp [brush,X1,laplace,delta]
   apply mul_left_cancel₀ (show (r:ℂ)≠0 by exact_mod_cast he); rw [lap1,← identity]; unfold Charge.change; simp_rw [mul_add, Finset.mul_sum, mul_left_comm (r:ℂ) (cross true _), ← mul_assoc,brushed]; simp_rw [mul_assoc (cross true _) (r:ℂ), brushed]; -- might distribute nested addition

-- to colors and periods. Parameter wave arbitrary emphasizing continuum projection later.
variable (f:Momentum D→Momentum D)
abbrev LegsK (r:ℝ) := Landau.choir (C:=A) (L0 r) f
abbrev LegsX (r:ℝ) := Landau.choir (C:=A) (X0 r) f
abbrev LegsY (r:ℝ) := Landau.choir (C:=A) (X1 r) f
lemma land_charge {K:YMflow D}(hh:∀ x,f (-x)= - f x) : (send (C:=A) f).change (Landau.choir K f)=Landau.choir ((stamp id).change K) f:= by
   funext i j q; simp only [Charge.change, Fintype.sum_prod_type, Landau.choir, send,hh];
   by_cases ht:i.2=j.2;
   · simp [ht, ite_mul,mul_ite]; rfl
   simp [ht, ite_mul, mul_ite]
lemma given (r:ℝ)(hh:∀ x,f (-x)= - f x) : (send (C:=A) f).change (LegsK f r)=LegsY f r:= by rw [LegsK,land_charge f hh,show ((stamp id).change (L0 r:YMflow D))=X1 r from funext fun i=> funext fun j=> funext (L_change r i j)]
lemma χ0 (i j:Atom D)(p:Momentum D): X0 (0:ℝ) i j p=laplace (fun _:Momentum D=>1) i j p:= by rw [X0, show Landau.low 0=fun _:Momentum D=> 1 from funext fun i=> (by simp [low, coat, Momentum.sq])] -- correct
omit [Fintype A] [Fintype D] [DecidableEq D] in
lemma reverse_one {K:YMflow D}(hk:Reverse K Landau.p)(hh:∀ x,f (-x)= - f x): Reverse (Landau.choir (C:=A) K f) Landau.parity:= by
   intro i j p'; by_cases ht:i.2=j.2; simp only [Landau.choir,if_pos ht, if_pos ht.symm,hh,hk,parity]; simp [Landau.choir,ht,Ne.symm ht]
omit [Fintype A] [Fintype D] [DecidableEq D] in
lemma closure {c:Bool}{K:YMflow D}(h:closed K Landau.p c): closed (Landau.choir (C:=A) K f) Landau.parity c:= by intro i j u; by_cases he:i.2=j.2; simp only [Landau.choir, if_pos he]; exact h _ _ _; simp [Landau.choir,he]
omit [DecidableEq D] in
lemma brush_neg (r:ℝ)(p:Momentum D): brush r (-p)=brush r p:= by simp [brush]
lemma L_rev (r:ℝ): Reverse (L0 (D:=D) r) Landau.p:= by rintro ⟨_|a,_|_⟩ ⟨_|b,_|_⟩ u <;> simp [L0,brush_neg,Landau.p,cross,realK]
lemma X_rev (r:ℝ): Reverse (X0 (D:=D) r) Landau.p:= by rintro ⟨_|a,_|_⟩ ⟨_|b,_|_⟩ u <;> simp [X0,low,coat,Landau.p,cross,laplace,scaling,delta,eq_comm]
lemma L_cl (r:ℝ): closed (L0 r) (Landau.p (A:=D)) false:= by rintro ⟨_|a,_|_⟩ ⟨_|b,_|_⟩ u <;> first | exact fun _=>rfl | simp [L0]
omit [Fintype D] in
lemma laplace_cl (c:Momentum D→ℝ): closed (laplace c) (Landau.p (A:=D)) true:= by rintro ⟨_|a,_|_⟩ ⟨_|b,_|_⟩ u <;> first| exact fun _=>rfl| simp [laplace]
-- field wave cost rho? smooth high D.
end YM.MS.City
